package com.syaq.tv;

import android.app.Activity;
import android.app.Notification;
import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.app.Service;
import android.content.Context;
import android.content.Intent;
import android.content.pm.ServiceInfo;
import android.graphics.Bitmap;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.LinearGradient;
import android.graphics.Paint;
import android.graphics.Path;
import android.graphics.PixelFormat;
import android.graphics.Rect;
import android.graphics.RectF;
import android.graphics.Shader;
import android.graphics.Typeface;
import android.graphics.drawable.BitmapDrawable;
import android.graphics.drawable.GradientDrawable;
import android.hardware.display.DisplayManager;
import android.hardware.display.VirtualDisplay;
import android.media.Image;
import android.media.ImageReader;
import android.media.projection.MediaProjection;
import android.media.projection.MediaProjectionManager;
import android.net.Uri;
import android.os.Build;
import android.os.Bundle;
import android.os.Handler;
import android.os.HandlerThread;
import android.os.IBinder;
import android.os.Looper;
import android.os.PowerManager;
import android.provider.Settings;
import android.text.TextPaint;
import android.util.DisplayMetrics;
import android.util.TypedValue;
import android.view.Gravity;
import android.view.View;
import android.view.ViewGroup;
import android.view.WindowManager;
import android.webkit.JavascriptInterface;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.widget.Button;
import android.widget.FrameLayout;
import android.widget.LinearLayout;
import android.widget.TextView;
import android.widget.Toast;

import com.google.mlkit.vision.common.InputImage;
import com.google.mlkit.vision.text.Text;
import com.google.mlkit.vision.text.TextRecognition;
import com.google.mlkit.vision.text.TextRecognizer;
import com.google.mlkit.vision.text.latin.TextRecognizerOptions;

import org.json.JSONArray;
import org.json.JSONObject;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.HttpURLConnection;
import java.net.URL;
import java.net.URLEncoder;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

public class MainActivity extends Activity {

    // ===== 1. الثوابت وإعدادات الأداء الفائق =====
    private static final String COLOR_ACCENT = "#F5A623";
    private static final String COLOR_ACCENT_LIGHT = "#FFD066";
    private static final String COLOR_BG = "#050507";
    private static final String COLOR_TEXT = "#FFFFFF";
    private static final String COLOR_TEXT_SOFT = "#C5CCD8";

    // فحص سريع كل 200ms لاقتناص النصوص فور ظهورها على الشاشة
    private static final long SCREEN_OCR_INTERVAL_MS = 200L;
    private static final long CAPTURE_TIMEOUT_MS = 1800L;
    private static final int PIXEL_BLOCK_SIZE = 12;

    // دقة 960x540 (نصف 1080p بالضبط) تضمن سرعة قراءة فورية وخفة تامة على معالج التلفزيون
    private static final int CAPTURE_W = 960;
    private static final int CAPTURE_H = 540;

    private static final int REQ_OVERLAY_PERMISSION = 101;
    private static final int REQ_MEDIA_PROJECTION = 102;

    // ===== 2. متغيرات البث الثابتة (Static) =====
    private static MediaProjection sMediaProjection;
    private static VirtualDisplay sVirtualDisplay;
    private static ImageReader sImageReader;
    private static Bitmap sLatestCleanGameBitmap;
    private static Bitmap sReusablePaddedBitmap;
    private static Bitmap sReusableOcrBitmap;

    // ===== 3. متغيرات الواجهة وحالة الوضع النشط =====
    private String roomCode;
    private boolean isArabic = true;
    private boolean isPhonePaired = false;

    private String currentTvSubMode = "camera";
    private boolean isScreenTranslationRunning = false;
    private String activeTranslatorEngine = "google_gtx";

    private TextView statusBadge;
    private TextView codeView;
    private WebView qrAndMqttWebView;

    private Button langToggleBtn;
    private Button btnTestBar;
    private Button btnNewCode;
    private Button btnPerm;
    private Button btnBroadcast;
    private Button btnUnpair;

    private LinearLayout centerClusterRow;
    private LinearLayout optionsColumn;
    private LinearLayout qrColumn;

    // ===== 4. متغيرات الطبقة الشفافة والمسار المزدوج (Dialogue Lane + HUD Cards) =====
    private WindowManager windowManager;
    private FrameLayout fullScreenOverlayStage;
    private FrameLayout screenItemsOverlayLayer; // حاوية بطاقات القوائم والإشعارات (HUD)
    private FrameLayout screenDialogueBannerBox; // شريط الحوارات السفلية المستقل في وضع الشاشة
    private TextView screenDialogueTextView;
    private GradientDrawable screenDialogueBg;

    private FrameLayout subtitleBannerBox;       // شريط ترجمة وضع الكاميرا
    private TextView subtitleTextView;
    private GradientDrawable boxBackground;
    private WindowManager.LayoutParams stageWindowParams;
    private PowerManager.WakeLock wakeLock;

    private MediaProjectionManager projectionManager;
    private TextRecognizer mlkitRecognizer;
    private volatile boolean isCapturingFrame = false;
    private volatile long lastCaptureStartTime = 0L;

    private HandlerThread ocrBackgroundThread;
    private Handler ocrBgHandler;
    private final Paint maskOverlayPaint = new Paint();

    // محرك الترجمة المباشرة المتوازي على التلفزيون
    private final ExecutorService fastDirectTranslatePool = Executors.newFixedThreadPool(4);
    private final ConcurrentHashMap<String, String> tvDirectTranslationCache = new ConcurrentHashMap<>();
    private final ConcurrentHashMap<String, String> instantGameDictionary = new ConcurrentHashMap<>();

    // كاشف تغير الإطار السريع لتجنب استهلاك المعالج عندما تكون الشاشة ثابتة
    private final int[] prevSampleGrid = new int[288];
    private boolean hasPrevSample = false;
    private long lastForcedOcrCheckTime = 0L;

    // تسلسل اللقطات وقفل منع اختفاء النصوص الثابتة (Anti-Flicker Lock)
    private long outgoingFrameSeq = 0L;
    private long lastAppliedOverlaySeq = 0L;
    private int consecutiveEmptyDialogueFrames = 0;
    private int consecutiveEmptyHudFrames = 0;
    private String lastSyncedDialogueToPhone = "";

    // تثبيت البطاقات مكانياً (Sticky View Cache) لمنع إعادة الرسم والاهتزاز
    private final Map<String, StickyHudCard> stickyHudCardMap = new HashMap<>();
    private final List<Rect> activeOverlayCaptureRects = Collections.synchronizedList(new ArrayList<Rect>());
    private String lastPublishedOcrSignature = "";
    private long lastPublishedOcrTime = 0L;
    private JSONArray lastScreenItemsArray = null;

    private int realScreenW = 1920;
    private int realScreenH = 1080;

    private JSONObject lastStyleJson = null;

    // ذاكرة الخطوط العربية
    private final Map<String, Typeface> customFontCache = new HashMap<>();
    private final ExecutorService fontDownloadExecutor = Executors.newSingleThreadExecutor();

    private static final String[][] GOOGLE_ARABIC_FONTS = new String[][]{
            {"IBMPlexSansArabic-Regular", "IBM+Plex+Sans+Arabic", "https://raw.githubusercontent.com/google/fonts/main/ofl/ibmplexsansarabic/IBMPlexSansArabic-Regular.ttf"},
            {"IBMPlexSansArabic-Bold", "IBM+Plex+Sans+Arabic", "https://raw.githubusercontent.com/google/fonts/main/ofl/ibmplexsansarabic/IBMPlexSansArabic-Bold.ttf"},
            {"ReadexPro-Regular", "Readex+Pro", "https://raw.githubusercontent.com/google/fonts/main/ofl/readexpro/ReadexPro%5BHEXP%2Cwght%5D.ttf"},
            {"ReadexPro-Bold", "Readex+Pro", "https://raw.githubusercontent.com/google/fonts/main/ofl/readexpro/ReadexPro%5BHEXP%2Cwght%5D.ttf"},
            {"Tajawal-Regular", "Tajawal", "https://raw.githubusercontent.com/google/fonts/main/ofl/tajawal/Tajawal-Regular.ttf"},
            {"Tajawal-Bold", "Tajawal", "https://raw.githubusercontent.com/google/fonts/main/ofl/tajawal/Tajawal-Bold.ttf"},
            {"Cairo-Regular", "Cairo", "https://raw.githubusercontent.com/google/fonts/main/ofl/cairo/Cairo%5Bslnt%2Cwght%5D.ttf"},
            {"Cairo-Bold", "Cairo", "https://raw.githubusercontent.com/google/fonts/main/ofl/cairo/Cairo%5Bslnt%2Cwght%5D.ttf"},
            {"Changa-Regular", "Changa", "https://raw.githubusercontent.com/google/fonts/main/ofl/changa/Changa%5Bwght%5D.ttf"},
            {"Changa-Bold", "Changa", "https://raw.githubusercontent.com/google/fonts/main/ofl/changa/Changa%5Bwght%5D.ttf"}
    };

    private final Handler uiHandler = new Handler(Looper.getMainLooper());
    private Runnable autoHideTestRunnable;

    private final Runnable keepAliveRunnable = new Runnable() {
        @Override
        public void run() {
            if (qrAndMqttWebView != null) {
                qrAndMqttWebView.resumeTimers();
            }
            uiHandler.postDelayed(this, 3000);
        }
    };

    private final Runnable screenOcrLoopRunnable = new Runnable() {
        @Override
        public void run() {
            if (isCapturingFrame && (System.currentTimeMillis() - lastCaptureStartTime > CAPTURE_TIMEOUT_MS)) {
                isCapturingFrame = false;
            }
            if (isPhonePaired
                    && "screen".equals(currentTvSubMode)
                    && isScreenTranslationRunning
                    && sImageReader != null
                    && !isCapturingFrame) {
                captureCleanGameScreenAndReadText();
            }
            uiHandler.postDelayed(this, SCREEN_OCR_INTERVAL_MS);
        }
    };

    private static class DetectedUiTextChunk {
        String text;
        Rect box;
        int lineCount;
        int avgLineHeight;
        String lane; // "dialogue" or "hud"

        DetectedUiTextChunk(String text, Rect box, int lineCount, int avgLineHeight, String lane) {
            this.text = text;
            this.box = new Rect(box);
            this.lineCount = lineCount;
            this.avgLineHeight = avgLineHeight;
            this.lane = lane;
        }
    }

    private static class StickyHudCard {
        String key;
        String arText;
        TextView view;
        Rect screenRect;
        Rect captureMaskRect;
        int missedFrames;

        StickyHudCard(String key, String arText, TextView view, Rect screenRect, Rect captureMaskRect) {
            this.key = key;
            this.arText = arText;
            this.view = view;
            this.screenRect = screenRect;
            this.captureMaskRect = captureMaskRect;
            this.missedFrames = 0;
        }
    }

    public class JsBridge {
        @JavascriptInterface
        public void onSyncEvent(final String jsonStr) {
            uiHandler.post(new Runnable() {
                @Override
                public void run() {
                    handleIncomingPhoneMessage(jsonStr);
                }
            });
        }
    }

    // الخدمة الأمامية لبث الشاشة مع دعم الإيقاف الفوري
    public static class SiyaqScreenCaptureService extends Service {
        public static final String ACTION_STOP_SERVICE = "SIYAQ_STOP_CAPTURE_SERVICE";

        @Override
        public int onStartCommand(Intent intent, int flags, int startId) {
            if (intent != null && ACTION_STOP_SERVICE.equals(intent.getAction())) {
                try {
                    stopForeground(true);
                    stopSelf();
                } catch (Exception ignored) {}
                return START_NOT_STICKY;
            }

            String channelId = "siyaq_tv_capture_channel";
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                NotificationChannel channel = new NotificationChannel(
                        channelId, "SIYAQ Screen Service", NotificationManager.IMPORTANCE_LOW);
                NotificationManager nm = getSystemService(NotificationManager.class);
                if (nm != null) nm.createNotificationChannel(channel);
            }
            Notification.Builder builder = Build.VERSION.SDK_INT >= Build.VERSION_CODES.O
                    ? new Notification.Builder(this, channelId)
                    : new Notification.Builder(this);
            Notification notification = builder
                    .setContentTitle("SIYAQ TV")
                    .setContentText("بث قراءة الشاشة نشط")
                    .setSmallIcon(android.R.drawable.ic_menu_view)
                    .build();

            try {
                if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {
                    startForeground(7711, notification, ServiceInfo.FOREGROUND_SERVICE_TYPE_MEDIA_PROJECTION);
                } else {
                    startForeground(7711, notification);
                }
            } catch (Exception ignored) {}
            return START_STICKY;
        }

        @Override
        public void onDestroy() {
            try {
                stopForeground(true);
            } catch (Exception ignored) {}
            super.onDestroy();
        }

        @Override
        public IBinder onBind(Intent intent) {
            return null;
        }
    }

    private void populateInstantGameDictionary() {
        String[][] entries = new String[][]{
                {"play", "تشغيل"}, {"pause", "إيقاف مؤقت"}, {"resume", "استئناف"}, {"continue", "متابعة"},
                {"start", "بدء"}, {"new game", "لعبة جديدة"}, {"load game", "تحميل لعبة"}, {"save game", "حفظ اللعبة"},
                {"save", "حفظ"}, {"load", "تحميل"}, {"settings", "الإعدادات"}, {"options", "الخيارات"},
                {"controls", "التحكم"}, {"display", "الشاشة"}, {"audio", "الصوت"}, {"video", "الفيديو"},
                {"graphics", "الرسومات"}, {"general", "عام"}, {"language", "اللغة"}, {"subtitles", "الترجمة"},
                {"back", "رجوع"}, {"exit", "خروج"}, {"quit", "إنهاء"}, {"close", "إغلاق"},
                {"cancel", "إلغاء"}, {"confirm", "تأكيد"}, {"accept", "قبول"}, {"decline", "رفض"},
                {"select", "تحديد"}, {"apply", "تطبيق"}, {"reset", "إعادة ضبط"}, {"default", "افتراضي"},
                {"next", "التالي"}, {"previous", "السابق"}, {"skip", "تخطي"}, {"home", "الرئيسية"},
                {"apps", "التطبيقات"}, {"library", "المكتبة"}, {"search", "بحث"}, {"download", "تحميل"},
                {"install", "تثبيت"}, {"delete", "حذف"}, {"update", "تحديث"}, {"sign in", "تسجيل الدخول"},
                {"account", "الحساب"}, {"network", "الشبكة"}, {"bluetooth", "البلوتوث"}, {"about", "حول"},
                {"restart", "إعادة التشغيل"}, {"on", "تشغيل"}, {"off", "إيقاف"}, {"enabled", "مفعّل"},
                {"disabled", "معطّل"}, {"high", "عالي"}, {"medium", "متوسط"}, {"low", "منخفض"},
                {"auto", "تلقائي"}, {"map", "الخريطة"}, {"inventory", "الحقيبة"}, {"items", "العناصر"},
                {"weapons", "الأسلحة"}, {"journal", "المذكرات"}, {"missions", "المهام"}, {"quests", "المهام"},
                {"skills", "المهارات"}, {"story", "القصة"}, {"online", "أونلاين"}, {"greet", "تحية"},
                {"antagonize", "استفزاز"}, {"rob", "سرقة"}, {"aim", "تصويب"}, {"shoot", "إطلاق"},
                {"mount", "ركوب"}, {"dismount", "نزول"}, {"flee", "إبعاد"}, {"calm", "تهدئة"},
                {"lead", "قيادة"}, {"brush", "تنظيف"}, {"feed", "إطعام"}, {"pat", "ملاطفة"},
                {"loot", "نهب"}, {"pick up", "التقاط"}, {"drop", "إسقاط"}, {"open", "فتح"},
                {"read", "قراءة"}, {"sit", "جلوس"}, {"sleep", "نوم"}, {"craft", "صناعة"},
                {"cook", "طبخ"}, {"buy", "شراء"}, {"sell", "بيع"}, {"donate", "تبرع"},
                {"upgrade", "ترقية"}, {"restock", "إعادة تزويد"}, {"yes", "نعم"}, {"no", "لا"},
                {"ok", "حسناً"}, {"okay", "حسناً"}, {"wait", "انتظر!"}, {"stop", "توقف!"},
                {"run", "اهرب!"}, {"go", "انطلق!"}, {"help", "النجدة!"}, {"follow me", "اتبعني"}
        };
        for (String[] pair : entries) {
            instantGameDictionary.put(pair[0], pair[1]);
        }
    }

    private Typeface strongFont() {
        return Typeface.create("sans-serif-medium", Typeface.BOLD);
    }

    private void preloadArabicGoogleFontsAsync() {
        fontDownloadExecutor.execute(new Runnable() {
            @Override
            public void run() {
                File fontDir = new File(getFilesDir(), "siyaq_fonts_v2");
                if (!fontDir.exists()) fontDir.mkdirs();
                boolean anyNewLoaded = false;

                for (String[] entry : GOOGLE_ARABIC_FONTS) {
                    String key = entry[0];
                    String cssFamily = entry[1];
                    String fallbackUrl = entry[2];
                    synchronized (customFontCache) {
                        if (customFontCache.containsKey(key)) continue;
                    }

                    File outFile = new File(fontDir, key + ".ttf");
                    if (!outFile.exists() || outFile.length() < 1000) {
                        try {
                            String weight = key.endsWith("Bold") ? "700" : "400";
                            String cssUrl = "https://fonts.googleapis.com/css?family=" + cssFamily + ":" + weight;
                            HttpURLConnection cssConn = (HttpURLConnection) new URL(cssUrl).openConnection();
                            cssConn.setRequestProperty("User-Agent", "Mozilla/5.0 (Linux; U; Android 4.4.2; en-us)");
                            cssConn.setConnectTimeout(4000);
                            cssConn.setReadTimeout(5000);
                            String directTtfUrl = fallbackUrl;
                            if (cssConn.getResponseCode() == 200) {
                                InputStream cis = cssConn.getInputStream();
                                byte[] cbuf = new byte[4096];
                                int cn = cis.read(cbuf);
                                cis.close();
                                if (cn > 0) {
                                    String cssText = new String(cbuf, 0, cn, "UTF-8");
                                    int idx = cssText.indexOf("https://fonts.gstatic.com/");
                                    if (idx != -1) {
                                        int endIdx = cssText.indexOf(")", idx);
                                        if (endIdx != -1) {
                                            directTtfUrl = cssText.substring(idx, endIdx).replace("\"", "").replace("'", "").trim();
                                        }
                                    }
                                }
                            }
                            cssConn.disconnect();

                            URL url = new URL(directTtfUrl);
                            HttpURLConnection conn = (HttpURLConnection) url.openConnection();
                            conn.setConnectTimeout(5000);
                            conn.setReadTimeout(7000);
                            conn.connect();
                            if (conn.getResponseCode() == 200) {
                                InputStream in = conn.getInputStream();
                                FileOutputStream out = new FileOutputStream(outFile);
                                byte[] buf = new byte[8192];
                                int n;
                                while ((n = in.read(buf)) != -1) out.write(buf, 0, n);
                                out.close();
                                in.close();
                            }
                            conn.disconnect();
                        } catch (Exception ignored) {}
                    }

                    if (outFile.exists() && outFile.length() > 1000) {
                        try {
                            Typeface tf = Typeface.createFromFile(outFile);
                            if (tf != null) {
                                synchronized (customFontCache) {
                                    customFontCache.put(key, tf);
                                }
                                anyNewLoaded = true;
                            }
                        } catch (Exception ignored) {}
                    }
                }

                if (anyNewLoaded && lastStyleJson != null) {
                    uiHandler.post(new Runnable() {
                        @Override
                        public void run() {
                            if ("camera".equals(currentTvSubMode)) {
                                applySmoothHardwareSubtitleStyle(lastStyleJson);
                            } else if (lastScreenItemsArray != null) {
                                clearAllStickyHudCards();
                                renderDualLaneScreenOverlays(lastScreenItemsArray, true);
                            }
                        }
                    });
                }
            }
        });
    }

    private Typeface resolveRequestedArabicTypeface(String fontFamilyRaw, boolean isBold) {
        String familyBase = "Tajawal";
        if (fontFamilyRaw != null) {
            if (fontFamilyRaw.contains("IBM") || fontFamilyRaw.contains("Plex")) familyBase = "IBMPlexSansArabic";
            else if (fontFamilyRaw.contains("Readex")) familyBase = "ReadexPro";
            else if (fontFamilyRaw.contains("Tajawal")) familyBase = "Tajawal";
            else if (fontFamilyRaw.contains("Cairo")) familyBase = "Cairo";
            else if (fontFamilyRaw.contains("Changa")) familyBase = "Changa";
        }
        String key = familyBase + (isBold ? "-Bold" : "-Regular");
        synchronized (customFontCache) {
            Typeface cached = customFontCache.get(key);
            if (cached != null) {
                return Typeface.create(cached, isBold ? Typeface.BOLD : Typeface.NORMAL);
            }
        }
        return Typeface.create("sans-serif-medium", isBold ? Typeface.BOLD : Typeface.NORMAL);
    }

    private class SiyaqWordmarkLogoView extends View {
        private final Paint whitePaint = new Paint(Paint.ANTI_ALIAS_FLAG);
        private final Paint accentBarPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
        private final Path sPath = new Path();
        private final Path yPath = new Path();
        private final Path aPath = new Path();
        private final Path qPath = new Path();
        private final RectF iRect = new RectF();

        public SiyaqWordmarkLogoView(Context context) {
            super(context);
            whitePaint.setColor(Color.WHITE);
            whitePaint.setStyle(Paint.Style.FILL);
        }

        @Override
        protected void onDraw(Canvas c) {
            super.onDraw(c);
            float w = getWidth();
            float h = getHeight();
            float scale = Math.min(w / 84f, h / 34f);
            float ox = (w - 100f * scale) / 2f;
            float oy = (h - 100f * scale) / 2f;

            sPath.reset();
            sPath.moveTo(ox + 11.1f * scale, oy + 35.1f * scale);
            sPath.lineTo(ox + 24.5f * scale, oy + 35.1f * scale);
            sPath.lineTo(ox + 24.5f * scale, oy + 39.2f * scale);
            sPath.lineTo(ox + 14.2f * scale, oy + 39.2f * scale);
            sPath.lineTo(ox + 14.2f * scale, oy + 46.3f * scale);
            sPath.lineTo(ox + 25.5f * scale, oy + 46.3f * scale);
            sPath.lineTo(ox + 25.5f * scale, oy + 64.6f * scale);
            sPath.lineTo(ox + 11.0f * scale, oy + 64.6f * scale);
            sPath.lineTo(ox + 11.0f * scale, oy + 59.2f * scale);
            sPath.lineTo(ox + 21.9f * scale, oy + 59.2f * scale);
            sPath.lineTo(ox + 21.9f * scale, oy + 51.4f * scale);
            sPath.lineTo(ox + 11.1f * scale, oy + 51.4f * scale);
            sPath.close();
            c.drawPath(sPath, whitePaint);

            accentBarPaint.setShader(new LinearGradient(
                    0, oy + 35.4f * scale, 0, oy + 64.9f * scale,
                    Color.parseColor(COLOR_ACCENT_LIGHT),
                    Color.parseColor(COLOR_ACCENT),
                    Shader.TileMode.CLAMP));
            iRect.set(ox + 29.5f * scale, oy + 35.4f * scale, ox + 34.1f * scale, oy + 64.9f * scale);
            c.drawRect(iRect, accentBarPaint);

            yPath.reset();
            yPath.moveTo(ox + 36.3f * scale, oy + 35.4f * scale);
            yPath.lineTo(ox + 41.3f * scale, oy + 35.4f * scale);
            yPath.lineTo(ox + 44.3f * scale, oy + 42.7f * scale);
            yPath.lineTo(ox + 47.4f * scale, oy + 35.4f * scale);
            yPath.lineTo(ox + 52.9f * scale, oy + 35.4f * scale);
            yPath.lineTo(ox + 47.3f * scale, oy + 46.4f * scale);
            yPath.lineTo(ox + 47.3f * scale, oy + 64.9f * scale);
            yPath.lineTo(ox + 41.4f * scale, oy + 64.9f * scale);
            yPath.lineTo(ox + 41.4f * scale, oy + 46.4f * scale);
            yPath.close();
            c.drawPath(yPath, whitePaint);

            aPath.reset();
            aPath.setFillType(Path.FillType.EVEN_ODD);
            aPath.moveTo(ox + 54.9f * scale, oy + 35.5f * scale);
            aPath.lineTo(ox + 68.9f * scale, oy + 35.5f * scale);
            aPath.lineTo(ox + 68.9f * scale, oy + 64.9f * scale);
            aPath.lineTo(ox + 64.5f * scale, oy + 64.9f * scale);
            aPath.lineTo(ox + 64.5f * scale, oy + 55.9f * scale);
            aPath.lineTo(ox + 59.3f * scale, oy + 55.9f * scale);
            aPath.lineTo(ox + 59.3f * scale, oy + 64.9f * scale);
            aPath.lineTo(ox + 54.9f * scale, oy + 64.9f * scale);
            aPath.close();
            aPath.moveTo(ox + 59.5f * scale, oy + 40.7f * scale);
            aPath.lineTo(ox + 64.6f * scale, oy + 40.7f * scale);
            aPath.lineTo(ox + 64.6f * scale, oy + 51.2f * scale);
            aPath.lineTo(ox + 59.5f * scale, oy + 51.2f * scale);
            aPath.close();
            c.drawPath(aPath, whitePaint);

            qPath.reset();
            qPath.setFillType(Path.FillType.EVEN_ODD);
            qPath.moveTo(ox + 71.7f * scale, oy + 35.5f * scale);
            qPath.lineTo(ox + 85.0f * scale, oy + 35.5f * scale);
            qPath.lineTo(ox + 85.0f * scale, oy + 59.8f * scale);
            qPath.lineTo(ox + 89.0f * scale, oy + 59.8f * scale);
            qPath.lineTo(ox + 86.1f * scale, oy + 64.9f * scale);
            qPath.lineTo(ox + 71.7f * scale, oy + 64.9f * scale);
            qPath.close();
            qPath.moveTo(ox + 74.8f * scale, oy + 39.2f * scale);
            qPath.lineTo(ox + 80.9f * scale, oy + 39.2f * scale);
            qPath.lineTo(ox + 80.9f * scale, oy + 59.8f * scale);
            qPath.lineTo(ox + 74.8f * scale, oy + 59.8f * scale);
            qPath.close();
            c.drawPath(qPath, whitePaint);
        }
    }

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);

        getWindow().addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
        getWindow().getDecorView().setLayoutDirection(View.LAYOUT_DIRECTION_LTR);

        maskOverlayPaint.setColor(Color.BLACK);
        maskOverlayPaint.setStyle(Paint.Style.FILL);
        populateInstantGameDictionary();

        ocrBackgroundThread = new HandlerThread("SiyaqOcrWorker", android.os.Process.THREAD_PRIORITY_BACKGROUND);
        ocrBackgroundThread.start();
        ocrBgHandler = new Handler(ocrBackgroundThread.getLooper());

        DisplayMetrics realDm = new DisplayMetrics();
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.JELLY_BEAN_MR1) {
            getWindowManager().getDefaultDisplay().getRealMetrics(realDm);
        } else {
            realDm = getResources().getDisplayMetrics();
        }
        realScreenW = realDm.widthPixels > 0 ? realDm.widthPixels : 1920;
        realScreenH = realDm.heightPixels > 0 ? realDm.heightPixels : 1080;

        mlkitRecognizer = TextRecognition.getClient(TextRecognizerOptions.DEFAULT_OPTIONS);
        projectionManager = (MediaProjectionManager) getSystemService(Context.MEDIA_PROJECTION_SERVICE);

        try {
            PowerManager pm = (PowerManager) getSystemService(POWER_SERVICE);
            if (pm != null) {
                wakeLock = pm.newWakeLock(PowerManager.PARTIAL_WAKE_LOCK, "siyaq:tvsync");
                wakeLock.acquire();
            }
        } catch (Exception ignored) {}

        preloadArabicGoogleFontsAsync();
        roomCode = generateRandomRoomCode();

        DisplayMetrics dm = getResources().getDisplayMetrics();
        int screenW = dm.widthPixels;
        int screenH = dm.heightPixels;

        FrameLayout rootFrame = new FrameLayout(this);
        rootFrame.setBackgroundColor(Color.parseColor(COLOR_BG));
        int padH = (int) (screenW * 0.05f);
        int padV = (int) (screenH * 0.04f);
        rootFrame.setPadding(padH, padV, padH, padV);

        langToggleBtn = new Button(this);
        langToggleBtn.setText("EN / ع");
        langToggleBtn.setFocusable(true);
        langToggleBtn.setFocusableInTouchMode(true);
        langToggleBtn.setBackgroundColor(Color.TRANSPARENT);
        langToggleBtn.setTextColor(Color.parseColor(COLOR_TEXT_SOFT));
        langToggleBtn.setTextSize(16);
        langToggleBtn.setTypeface(strongFont());
        langToggleBtn.setPadding(20, 10, 20, 10);
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.LOLLIPOP) {
            langToggleBtn.setStateListAnimator(null);
            langToggleBtn.setElevation(0f);
        }
        langToggleBtn.setOnFocusChangeListener(new View.OnFocusChangeListener() {
            @Override
            public void onFocusChange(View v, boolean hasFocus) {
                langToggleBtn.setTextColor(hasFocus ? Color.parseColor(COLOR_ACCENT) : Color.parseColor(COLOR_TEXT_SOFT));
                langToggleBtn.setTextSize(hasFocus ? 18 : 16);
            }
        });
        langToggleBtn.setOnClickListener(new View.OnClickListener() {
            @Override
            public void onClick(View v) {
                isArabic = !isArabic;
                applyLanguageAndLayoutDirection();
            }
        });

        FrameLayout.LayoutParams langLp = new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT,
                Gravity.TOP | Gravity.LEFT);
        rootFrame.addView(langToggleBtn, langLp);

        LinearLayout topLogoContainer = new LinearLayout(this);
        topLogoContainer.setOrientation(LinearLayout.VERTICAL);
        topLogoContainer.setGravity(Gravity.CENTER);

        int logoW = Math.max(150, (int) (screenW * 0.16f));
        int logoH = Math.max(54, (int) (screenH * 0.085f));
        SiyaqWordmarkLogoView wordmarkView = new SiyaqWordmarkLogoView(this);
        topLogoContainer.addView(wordmarkView, new LinearLayout.LayoutParams(logoW, logoH));

        statusBadge = new TextView(this);
        statusBadge.setText("غير متصل");
        statusBadge.setTextColor(Color.parseColor(COLOR_TEXT_SOFT));
        statusBadge.setTextSize(14);
        statusBadge.setTypeface(strongFont());
        statusBadge.setGravity(Gravity.CENTER);
        statusBadge.setPadding(0, 6, 0, 0);
        topLogoContainer.addView(statusBadge);

        FrameLayout.LayoutParams topLogoLp = new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT,
                Gravity.TOP | Gravity.CENTER_HORIZONTAL);
        rootFrame.addView(topLogoContainer, topLogoLp);

        centerClusterRow = new LinearLayout(this);
        centerClusterRow.setOrientation(LinearLayout.HORIZONTAL);
        centerClusterRow.setGravity(Gravity.CENTER);

        qrColumn = new LinearLayout(this);
        qrColumn.setOrientation(LinearLayout.VERTICAL);
        qrColumn.setGravity(Gravity.CENTER);
        qrColumn.setPadding(36, 16, 36, 16);

        int qrBoxSize = Math.min(215, (int) (screenH * 0.38f));
        qrAndMqttWebView = new WebView(this) {
            @Override
            protected void onWindowVisibilityChanged(int visibility) {
                super.onWindowVisibilityChanged(View.VISIBLE);
            }
        };
        qrAndMqttWebView.setBackgroundColor(Color.TRANSPARENT);
        qrAndMqttWebView.setVerticalScrollBarEnabled(false);
        qrAndMqttWebView.setHorizontalScrollBarEnabled(false);
        WebSettings ws = qrAndMqttWebView.getSettings();
        ws.setJavaScriptEnabled(true);
        ws.setDomStorageEnabled(true);
        qrAndMqttWebView.addJavascriptInterface(new JsBridge(), "SiyaqTvWaitBridge");

        qrColumn.addView(qrAndMqttWebView, new LinearLayout.LayoutParams(qrBoxSize, qrBoxSize));

        codeView = new TextView(this);
        codeView.setText(roomCode);
        codeView.setTextColor(Color.parseColor(COLOR_ACCENT));
        codeView.setTextSize(26);
        codeView.setTypeface(Typeface.MONOSPACE, Typeface.BOLD);
        codeView.setGravity(Gravity.CENTER);
        codeView.setPadding(0, 22, 0, 0);
        qrColumn.addView(codeView);

        optionsColumn = new LinearLayout(this);
        optionsColumn.setOrientation(LinearLayout.VERTICAL);
        optionsColumn.setGravity(Gravity.CENTER_VERTICAL);
        optionsColumn.setPadding(36, 12, 36, 12);

        btnTestBar = createCleanTextButton("اختبار شريط الترجمة", new View.OnClickListener() {
            @Override
            public void onClick(View v) {
                triggerTestSubtitleBanner();
            }
        });
        optionsColumn.addView(btnTestBar);

        btnNewCode = createCleanTextButton("تجديد رمز الاقتران", new View.OnClickListener() {
            @Override
            public void onClick(View v) {
                rotateToFreshRoomCode();
                Toast.makeText(MainActivity.this, isArabic ? "تم تجديد الرمز" : "Code refreshed", Toast.LENGTH_SHORT).show();
            }
        });
        optionsColumn.addView(btnNewCode);

        btnPerm = createCleanTextButton("تفعيل صلاحية الشاشة", new View.OnClickListener() {
            @Override
            public void onClick(View v) {
                requestOverlayPermissionOnly();
            }
        });
        optionsColumn.addView(btnPerm);

        btnBroadcast = createCleanTextButton("تفعيل وضع البث", new View.OnClickListener() {
            @Override
            public void onClick(View v) {
                if (sMediaProjection != null || sImageReader != null) {
                    stopScreenBroadcastCompletely();
                    Toast.makeText(MainActivity.this,
                            isArabic ? "تم إيقاف وضع البث نهائياً ✓" : "Screen Broadcast Stopped ✓",
                            Toast.LENGTH_SHORT).show();
                } else {
                    requestScreenBroadcastOnly();
                }
            }
        });
        optionsColumn.addView(btnBroadcast);

        btnUnpair = createCleanTextButton("إلغاء الاقتران", new View.OnClickListener() {
            @Override
            public void onClick(View v) {
                performCleanUnpairAndRotateCode();
            }
        });
        optionsColumn.addView(btnUnpair);

        FrameLayout.LayoutParams centerLp = new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT,
                Gravity.CENTER);
        centerLp.topMargin = (int) (screenH * 0.04f);
        rootFrame.addView(centerClusterRow, centerLp);

        setContentView(rootFrame);

        applyLanguageAndLayoutDirection();
        btnTestBar.requestFocus();
        loadQrAndWaitBridge();
        uiHandler.post(keepAliveRunnable);
        uiHandler.post(screenOcrLoopRunnable);
    }

    private String generateRandomRoomCode() {
        int num = 10000000 + new Random().nextInt(90000000);
        return String.valueOf(num);
    }

    private void applyLanguageAndLayoutDirection() {
        centerClusterRow.removeAllViews();

        LinearLayout.LayoutParams colLp = new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT);
        colLp.setMargins(96, 0, 96, 0);

        boolean overlayReady = canDrawOverlaySafely();
        boolean broadcastReady = (sMediaProjection != null && sImageReader != null);

        if (isArabic) {
            centerClusterRow.addView(qrColumn, colLp);
            centerClusterRow.addView(optionsColumn, colLp);

            btnTestBar.setText("اختبار شريط الترجمة");
            btnNewCode.setText("تجديد رمز الاقتران");
            btnPerm.setText(overlayReady ? "صلاحية الشاشة: مفعّلة ✓" : "تفعيل صلاحية الشاشة");
            btnBroadcast.setText(broadcastReady ? "إيقاف وضع البث ■" : "تفعيل وضع البث");
            btnUnpair.setText("إلغاء الاقتران");

            int rightGrav = Gravity.RIGHT | Gravity.CENTER_VERTICAL;
            btnTestBar.setGravity(rightGrav);
            btnNewCode.setGravity(rightGrav);
            btnPerm.setGravity(rightGrav);
            btnBroadcast.setGravity(rightGrav);
            btnUnpair.setGravity(rightGrav);
        } else {
            centerClusterRow.addView(optionsColumn, colLp);
            centerClusterRow.addView(qrColumn, colLp);

            btnTestBar.setText("Test Subtitle Bar");
            btnNewCode.setText("Refresh Pair Code");
            btnPerm.setText(overlayReady ? "Screen Permission: Active ✓" : "Enable Screen Permission");
            btnBroadcast.setText(broadcastReady ? "Stop Screen Broadcast ■" : "Enable Screen Broadcast");
            btnUnpair.setText("Unpair Device");

            int leftGrav = Gravity.LEFT | Gravity.CENTER_VERTICAL;
            btnTestBar.setTextAlignment(View.TEXT_ALIGNMENT_VIEW_START);
            btnTestBar.setGravity(leftGrav);
            btnNewCode.setGravity(leftGrav);
            btnPerm.setGravity(leftGrav);
            btnBroadcast.setGravity(leftGrav);
            btnUnpair.setGravity(leftGrav);
        }

        updateUiForPairingState(isPhonePaired);
    }

    @Override
    protected void onResume() {
        super.onResume();
        applyLanguageAndLayoutDirection();
    }

    @Override
    protected void onPause() {
        super.onPause();
        if (qrAndMqttWebView != null) {
            qrAndMqttWebView.onResume();
            qrAndMqttWebView.resumeTimers();
        }
    }

    @Override
    protected void onStop() {
        super.onStop();
        if (qrAndMqttWebView != null) {
            qrAndMqttWebView.onResume();
            qrAndMqttWebView.resumeTimers();
        }
    }

    private Button createCleanTextButton(String label, View.OnClickListener listener) {
        final Button btn = new Button(this);
        btn.setText(label);
        btn.setFocusable(true);
        btn.setFocusableInTouchMode(true);
        btn.setBackgroundColor(Color.TRANSPARENT);
        btn.setTextColor(Color.parseColor(COLOR_TEXT));
        btn.setTextSize(18);
        btn.setTypeface(strongFont());
        btn.setPadding(20, 14, 20, 14);
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.LOLLIPOP) {
            btn.setStateListAnimator(null);
            btn.setElevation(0f);
        }

        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT);
        lp.setMargins(0, 8, 0, 8);
        btn.setLayoutParams(lp);

        btn.setOnFocusChangeListener(new View.OnFocusChangeListener() {
            @Override
            public void onFocusChange(View v, boolean hasFocus) {
                if (hasFocus) {
                    btn.setTextColor(Color.parseColor(COLOR_ACCENT));
                    btn.setTextSize(20);
                } else {
                    btn.setTextColor(Color.parseColor(COLOR_TEXT));
                    btn.setTextSize(18);
                }
            }
        });

        btn.setOnClickListener(listener);
        return btn;
    }

    private boolean canDrawOverlaySafely() {
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.M) return true;
        try {
            return Settings.canDrawOverlays(this);
        } catch (Exception e) {
            return false;
        }
    }

    private void requestOverlayPermissionOnly() {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M && !canDrawOverlaySafely()) {
            try {
                Intent intent = new Intent(Settings.ACTION_MANAGE_OVERLAY_PERMISSION,
                        Uri.parse("package:" + getPackageName()));
                startActivityForResult(intent, REQ_OVERLAY_PERMISSION);
                return;
            } catch (Exception e1) {
                try {
                    Intent fallbackIntent = new Intent(Settings.ACTION_MANAGE_OVERLAY_PERMISSION);
                    startActivityForResult(fallbackIntent, REQ_OVERLAY_PERMISSION);
                    return;
                } catch (Exception e2) {
                    ensureOverlayStageCreated();
                    Toast.makeText(this, isArabic ? "تم تفعيل الطبقة المتوافقة مع التلفاز ✓" : "TV Overlay Active ✓", Toast.LENGTH_SHORT).show();
                    return;
                }
            }
        }
        ensureOverlayStageCreated();
        applyLanguageAndLayoutDirection();
        Toast.makeText(this, isArabic ? "صلاحية الشاشة مفعّلة ✓" : "Screen Permission Active ✓", Toast.LENGTH_SHORT).show();
    }

    private void requestScreenBroadcastOnly() {
        if (sMediaProjection != null && sImageReader != null) {
            applyLanguageAndLayoutDirection();
            return;
        }

        try {
            if (projectionManager == null) {
                projectionManager = (MediaProjectionManager) getSystemService(Context.MEDIA_PROJECTION_SERVICE);
            }
            if (projectionManager != null) {
                startActivityForResult(projectionManager.createScreenCaptureIntent(), REQ_MEDIA_PROJECTION);
            }
        } catch (Exception e) {
            Toast.makeText(this, isArabic ? "تعذر فتح نافذة البث" : "Broadcast error", Toast.LENGTH_LONG).show();
        }
    }

    private void clearAllStickyHudCards() {
        stickyHudCardMap.clear();
        if (screenItemsOverlayLayer != null) {
            screenItemsOverlayLayer.removeAllViews();
        }
        if (screenDialogueBannerBox != null) {
            screenDialogueBannerBox.setVisibility(View.GONE);
            if (screenDialogueTextView != null) screenDialogueTextView.setText("");
        }
        activeOverlayCaptureRects.clear();
    }

    private void stopScreenBroadcastCompletely() {
        isScreenTranslationRunning = false;
        isCapturingFrame = false;
        hasPrevSample = false;
        consecutiveEmptyDialogueFrames = 0;
        consecutiveEmptyHudFrames = 0;
        lastPublishedOcrSignature = "";
        lastSyncedDialogueToPhone = "";
        lastScreenItemsArray = null;

        clearAllStickyHudCards();
        releaseScreenCaptureResources();

        try {
            Intent stopSvc = new Intent(this, SiyaqScreenCaptureService.class);
            stopSvc.setAction(SiyaqScreenCaptureService.ACTION_STOP_SERVICE);
            stopService(stopSvc);
        } catch (Exception ignored) {}

        applyLanguageAndLayoutDirection();
    }

    @Override
    protected void onActivityResult(int requestCode, final int resultCode, final Intent data) {
        super.onActivityResult(requestCode, resultCode, data);

        if (requestCode == REQ_OVERLAY_PERMISSION) {
            ensureOverlayStageCreated();
            applyLanguageAndLayoutDirection();
            Toast.makeText(this, isArabic ? "تم تفعيل صلاحية الشاشة ✓" : "Permission Active ✓", Toast.LENGTH_SHORT).show();
        } else if (requestCode == REQ_MEDIA_PROJECTION) {
            if (resultCode == Activity.RESULT_OK && data != null) {
                try {
                    Intent svcIntent = new Intent(this, SiyaqScreenCaptureService.class);
                    if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                        startForegroundService(svcIntent);
                    } else {
                        startService(svcIntent);
                    }
                } catch (Exception ignored) {}

                uiHandler.postDelayed(new Runnable() {
                    @Override
                    public void run() {
                        setupVirtualDisplayReader(resultCode, data);
                        applyLanguageAndLayoutDirection();
                        Toast.makeText(MainActivity.this,
                                isArabic ? "تم تفعيل وضع البث بنجاح ✓" : "Broadcast Enabled ✓",
                                Toast.LENGTH_SHORT).show();
                        if (isPhonePaired && "screen".equals(currentTvSubMode)) {
                            moveTaskToBack(true);
                        }
                    }
                }, 250);
            } else {
                Toast.makeText(this, isArabic ? "يرجى اختيار (البدء الآن) لتفعيل البث" : "Select Start Now", Toast.LENGTH_SHORT).show();
            }
        }
    }

    private void setupVirtualDisplayReader(int resultCode, Intent data) {
        try {
            releaseScreenCaptureResources();
            if (projectionManager == null) {
                projectionManager = (MediaProjectionManager) getSystemService(Context.MEDIA_PROJECTION_SERVICE);
            }
            sMediaProjection = projectionManager.getMediaProjection(resultCode, data);
            if (sMediaProjection == null) return;

            sMediaProjection.registerCallback(new MediaProjection.Callback() {
                @Override
                public void onStop() {
                    super.onStop();
                    uiHandler.post(new Runnable() {
                        @Override
                        public void run() {
                            stopScreenBroadcastCompletely();
                        }
                    });
                }
            }, uiHandler);

            int dpi = getResources().getDisplayMetrics().densityDpi;
            sImageReader = ImageReader.newInstance(CAPTURE_W, CAPTURE_H, PixelFormat.RGBA_8888, 3);
            sVirtualDisplay = sMediaProjection.createVirtualDisplay(
                    "SiyaqTvCapture",
                    CAPTURE_W,
                    CAPTURE_H,
                    dpi,
                    DisplayManager.VIRTUAL_DISPLAY_FLAG_AUTO_MIRROR,
                    sImageReader.getSurface(),
                    null,
                    ocrBgHandler != null ? ocrBgHandler : uiHandler
            );
            ensureOverlayStageCreated();
        } catch (Exception e) {
            Toast.makeText(this, "خطأ في بدء البث: " + e.getMessage(), Toast.LENGTH_LONG).show();
        }
    }

    private void triggerTestSubtitleBanner() {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M && !canDrawOverlaySafely()) {
            requestOverlayPermissionOnly();
            return;
        }
        ensureOverlayStageCreated();
        if (subtitleBannerBox != null && subtitleTextView != null) {
            clearAllStickyHudCards();
            subtitleTextView.setText(isArabic
                    ? "اختبار شريط الترجمة — جاهز للعرض فوق اللعبة"
                    : "Subtitle Bar Test — Ready over game");
            subtitleBannerBox.setVisibility(View.VISIBLE);
            positionBannerAccurately(subtitleBannerBox, 0.50f, 0.82f);

            if (autoHideTestRunnable != null) {
                uiHandler.removeCallbacks(autoHideTestRunnable);
            }
            autoHideTestRunnable = new Runnable() {
                @Override
                public void run() {
                    if (subtitleBannerBox != null && !isPhonePaired) {
                        subtitleBannerBox.setVisibility(View.GONE);
                    }
                }
            };
            uiHandler.postDelayed(autoHideTestRunnable, 4000);
        }
    }

    private void loadQrAndWaitBridge() {
        String qrData = "SIYAQ-TV-" + roomCode;
        String qrUrl = "https://api.qrserver.com/v1/create-qr-code/?size=300x300&ecc=M&margin=2&data=" + qrData;

        String html = "<!DOCTYPE html><html><head>" +
                "<style>" +
                "*{margin:0;padding:0;box-sizing:border-box;}" +
                "html,body{width:100%;height:100%;background:transparent;display:flex;align-items:center;justify-content:center;overflow:hidden;}" +
                ".card{width:92%;height:92%;background:#FFFFFF;border-radius:20px;display:flex;align-items:center;justify-content:center;padding:11%;}" +
                "img{width:100%;height:100%;object-fit:contain;display:block;image-rendering:pixelated;}" +
                "</style>" +
                "<script src='https://unpkg.com/mqtt/dist/mqtt.min.js'></script>" +
                "</head><body>" +
                "<div class='card'><img src='" + qrUrl + "' alt='QR' /></div>" +
                "<script>" +
                "window.mqttClient = null;" +
                "try {" +
                "  window.mqttClient = mqtt.connect('wss://broker.emqx.io:8084/mqtt', {" +
                "    keepalive: 20," +
                "    reconnectPeriod: 800," +
                "    clean: true" +
                "  });" +
                "  window.mqttClient.on('connect', () => { window.mqttClient.subscribe('siyaq/tv/sec/" + roomCode + "'); });" +
                "  window.mqttClient.on('message', (t, p) => { SiyaqTvWaitBridge.onSyncEvent(p.toString()); });" +
                "} catch(e) {}" +
                "</script></body></html>";
        qrAndMqttWebView.loadDataWithBaseURL("https://siyaq.app", html, "text/html", "UTF-8", null);
    }

    private void applyStyleMetadata(JSONObject style) {
        if (style == null) return;
        lastStyleJson = style;
        String eng = style.optString("translatorEngine", "");
        if (!eng.isEmpty()) {
            activeTranslatorEngine = eng;
        }
    }

    private void handleIncomingPhoneMessage(String jsonStr) {
        try {
            JSONObject obj = new JSONObject(jsonStr);
            if ("tv".equals(obj.optString("sender", ""))) return;

            String type = obj.optString("type", "");

            if ("UNPAIRED".equals(type)) {
                stopScreenBroadcastCompletely();
                hideOverlayStage();
                isPhonePaired = false;
                updateUiForPairingState(false);
                rotateToFreshRoomCode();
                Toast.makeText(this, isArabic ? "تم إلغاء الاقتران وإيقاف البث" : "Unpaired & Broadcast Stopped", Toast.LENGTH_SHORT).show();
                return;
            }

            if ("SUB_CLEAR".equals(type)) {
                if (subtitleBannerBox != null) {
                    subtitleTextView.setText("");
                    subtitleBannerBox.setVisibility(View.GONE);
                }
                clearAllStickyHudCards();
                lastPublishedOcrSignature = "";
                lastSyncedDialogueToPhone = "";
                lastScreenItemsArray = null;
                return;
            }

            if ("STYLE_UPDATE".equals(type)) {
                JSONObject style = obj.optJSONObject("style");
                if (style != null) {
                    applyStyleMetadata(style);
                    if ("camera".equals(currentTvSubMode)) {
                        applySmoothHardwareSubtitleStyle(style);
                    } else if (lastScreenItemsArray != null) {
                        renderDualLaneScreenOverlays(lastScreenItemsArray, true);
                    }
                }
                return;
            }

            if ("TV_MODE_SWITCH".equals(type)) {
                String mode = obj.optString("mode", "");
                String subMode = obj.optString("tvSubMode", "");
                boolean active = obj.optBoolean("active", false);
                JSONObject style = obj.optJSONObject("style");
                if (style != null) applyStyleMetadata(style);

                if ("screen_ocr".equals(mode) || "screen".equals(subMode)) {
                    currentTvSubMode = "screen";
                    isScreenTranslationRunning = active;
                    lastPublishedOcrSignature = "";
                    hasPrevSample = false;
                    consecutiveEmptyDialogueFrames = 0;
                    consecutiveEmptyHudFrames = 0;

                    if (subtitleBannerBox != null) {
                        subtitleTextView.setText("");
                        subtitleBannerBox.setVisibility(View.GONE);
                    }
                    if (!active) {
                        clearAllStickyHudCards();
                        lastScreenItemsArray = null;
                    }

                    updateUiForPairingState(isPhonePaired);

                    if (active) {
                        if (sMediaProjection != null && sImageReader != null) {
                            captureCleanGameScreenAndReadText();
                        } else {
                            Intent bringFront = new Intent(this, MainActivity.class);
                            bringFront.addFlags(Intent.FLAG_ACTIVITY_REORDER_TO_FRONT | Intent.FLAG_ACTIVITY_SINGLE_TOP);
                            startActivity(bringFront);
                            requestScreenBroadcastOnly();
                        }
                    }
                } else {
                    currentTvSubMode = "camera";
                    isScreenTranslationRunning = false;
                    clearAllStickyHudCards();
                    lastScreenItemsArray = null;
                    updateUiForPairingState(isPhonePaired);
                }
                return;
            }

            if ("PAIRED".equals(type)) {
                isPhonePaired = true;
                ensureOverlayStageCreated();

                String incomingSubMode = obj.optString("tvSubMode", "camera");
                currentTvSubMode = "screen".equals(incomingSubMode) ? "screen" : "camera";
                isScreenTranslationRunning = obj.optBoolean("active", false);
                lastPublishedOcrSignature = "";
                hasPrevSample = false;
                consecutiveEmptyDialogueFrames = 0;
                consecutiveEmptyHudFrames = 0;

                JSONObject style = obj.optJSONObject("style");
                if (style != null) applyStyleMetadata(style);

                updateUiForPairingState(true);

                if ("screen".equals(currentTvSubMode)) {
                    if (subtitleBannerBox != null) subtitleBannerBox.setVisibility(View.GONE);
                    if (sMediaProjection == null || sImageReader == null) {
                        Toast.makeText(this, isArabic ? "تم الاقتران (وضع الشاشة) — اختر البدء الآن لتفعيل البث" : "Paired (Screen Mode) — Allow Broadcast", Toast.LENGTH_LONG).show();
                        requestScreenBroadcastOnly();
                    } else {
                        Toast.makeText(this, isArabic ? "تم الاقتران (وضع الشاشة جاهز ✓)" : "Paired (Screen Mode Ready ✓)", Toast.LENGTH_SHORT).show();
                        moveTaskToBack(true);
                    }
                } else {
                    clearAllStickyHudCards();
                    lastScreenItemsArray = null;
                    subtitleTextView.setText(isArabic ? "متصل بالجوال (وضع الكاميرا) — جاهز للترجمة" : "Connected (Camera Mode) — Ready");
                    subtitleBannerBox.setVisibility(View.VISIBLE);
                    if (lastStyleJson != null) {
                        applySmoothHardwareSubtitleStyle(lastStyleJson);
                    } else {
                        positionBannerAccurately(subtitleBannerBox, 0.50f, 0.82f);
                    }
                    Toast.makeText(this, isArabic ? "تم الاقتران (وضع الكاميرا ✓)" : "Paired (Camera Mode ✓)", Toast.LENGTH_SHORT).show();
                    moveTaskToBack(true);
                }
                return;
            }

            if ("SCREEN_OVERLAY_BATCH".equals(type)) {
                if (!"screen".equals(currentTvSubMode)) return;
                if (!isPhonePaired) {
                    isPhonePaired = true;
                    updateUiForPairingState(true);
                }
                long seq = obj.optLong("frameSeq", 0L);
                if (seq > 0L && seq < lastAppliedOverlaySeq) {
                    return;
                }
                if (seq > 0L) lastAppliedOverlaySeq = seq;

                ensureOverlayStageCreated();
                JSONObject style = obj.optJSONObject("style");
                if (style != null) applyStyleMetadata(style);

                JSONArray incomingItems = obj.optJSONArray("items");
                lastScreenItemsArray = (incomingItems != null && incomingItems.length() > 0) ? incomingItems : null;
                renderDualLaneScreenOverlays(lastScreenItemsArray, false);
                return;
            }

            if ("SUB_UPDATE".equals(type)) {
                if ("screen".equals(currentTvSubMode) && !"camera".equals(obj.optString("tvSubMode", ""))) {
                    return;
                }
                currentTvSubMode = "camera";

                if (!isPhonePaired) {
                    isPhonePaired = true;
                    updateUiForPairingState(true);
                }
                ensureOverlayStageCreated();
                clearAllStickyHudCards();
                lastScreenItemsArray = null;

                JSONObject style = obj.optJSONObject("style");
                if (style != null) applyStyleMetadata(style);

                String text = obj.optString("text", "").replace("✓", "").trim();
                if (text.isEmpty()
                        || "في انتظار الترجمات".equals(text)
                        || "في انتظار الترجمة".equals(text)
                        || "الترجمة متوقفة".equals(text)
                        || "Waiting for subtitles".equals(text)
                        || "Waiting for translation".equals(text)
                        || "Translation Paused".equals(text)) {
                    subtitleTextView.setText("");
                    subtitleBannerBox.setVisibility(View.GONE);
                } else {
                    subtitleTextView.setText(text);
                    subtitleBannerBox.setVisibility(View.VISIBLE);
                    if (lastStyleJson != null) {
                        applySmoothHardwareSubtitleStyle(lastStyleJson);
                    } else {
                        positionBannerAccurately(subtitleBannerBox, 0.50f, 0.82f);
                    }
                }
            }
        } catch (Exception ignored) {}
    }

    // ===== 7. كاشف تغير الإطار الفوري (< 0.4ms) لقراءة فورية دون ثقل على يوتيوب =====
    private boolean didScreenChangeFast(Bitmap bmp) {
        int stepX = CAPTURE_W / 24;
        int stepY = CAPTURE_H / 12;
        int idx = 0;
        long diffSum = 0L;
        int changedCells = 0;

        for (int y = stepY / 2; y < CAPTURE_H && idx < 288; y += stepY) {
            for (int x = stepX / 2; x < CAPTURE_W && idx < 288; x += stepX) {
                int px = bmp.getPixel(x, y);
                int lum = (((px >> 16) & 0xFF) * 77 + ((px >> 8) & 0xFF) * 150 + (px & 0xFF) * 29) >> 8;
                if (hasPrevSample) {
                    int d = Math.abs(lum - prevSampleGrid[idx]);
                    diffSum += d;
                    if (d >= 15) changedCells++;
                }
                prevSampleGrid[idx] = lum;
                idx++;
            }
        }

        if (!hasPrevSample) {
            hasPrevSample = true;
            return true;
        }
        return changedCells >= 2 || (diffSum / 288L) >= 2L;
    }

    private void captureCleanGameScreenAndReadText() {
        if (sImageReader == null || mlkitRecognizer == null || ocrBgHandler == null) return;
        isCapturingFrame = true;
        lastCaptureStartTime = System.currentTimeMillis();

        ocrBgHandler.post(new Runnable() {
            @Override
            public void run() {
                Image img = null;
                try {
                    if (sImageReader == null) {
                        isCapturingFrame = false;
                        return;
                    }
                    img = sImageReader.acquireLatestImage();
                    if (img != null) {
                        Image.Plane[] planes = img.getPlanes();
                        ByteBuffer buffer = planes[0].getBuffer();
                        int pixelStride = planes[0].getPixelStride();
                        int rowStride = planes[0].getRowStride();
                        int rowPadding = rowStride - pixelStride * CAPTURE_W;
                        int paddedW = CAPTURE_W + Math.max(0, rowPadding / pixelStride);

                        if (sReusablePaddedBitmap == null
                                || sReusablePaddedBitmap.isRecycled()
                                || sReusablePaddedBitmap.getWidth() != paddedW
                                || sReusablePaddedBitmap.getHeight() != CAPTURE_H) {
                            if (sReusablePaddedBitmap != null && !sReusablePaddedBitmap.isRecycled()) {
                                sReusablePaddedBitmap.recycle();
                            }
                            sReusablePaddedBitmap = Bitmap.createBitmap(paddedW, CAPTURE_H, Bitmap.Config.ARGB_8888);
                        }
                        buffer.rewind();
                        sReusablePaddedBitmap.copyPixelsFromBuffer(buffer);
                        img.close();
                        img = null;

                        if (sLatestCleanGameBitmap == null
                                || sLatestCleanGameBitmap.isRecycled()
                                || sLatestCleanGameBitmap.getWidth() != CAPTURE_W
                                || sLatestCleanGameBitmap.getHeight() != CAPTURE_H) {
                            sLatestCleanGameBitmap = Bitmap.createBitmap(CAPTURE_W, CAPTURE_H, Bitmap.Config.ARGB_8888);
                        }
                        Canvas cleanCanvas = new Canvas(sLatestCleanGameBitmap);
                        cleanCanvas.drawBitmap(
                                sReusablePaddedBitmap,
                                new Rect(0, 0, CAPTURE_W, CAPTURE_H),
                                new Rect(0, 0, CAPTURE_W, CAPTURE_H),
                                null
                        );
                    }

                    if (sLatestCleanGameBitmap == null || sLatestCleanGameBitmap.isRecycled()) {
                        isCapturingFrame = false;
                        return;
                    }

                    long now = System.currentTimeMillis();
                    boolean frameMoved = didScreenChangeFast(sLatestCleanGameBitmap);
                    if (!frameMoved && (now - lastForcedOcrCheckTime) < 850L) {
                        isCapturingFrame = false;
                        return;
                    }
                    lastForcedOcrCheckTime = now;

                    if (sReusableOcrBitmap == null
                            || sReusableOcrBitmap.isRecycled()
                            || sReusableOcrBitmap.getWidth() != CAPTURE_W
                            || sReusableOcrBitmap.getHeight() != CAPTURE_H) {
                        sReusableOcrBitmap = Bitmap.createBitmap(CAPTURE_W, CAPTURE_H, Bitmap.Config.ARGB_8888);
                    }

                    Canvas ocrCanvas = new Canvas(sReusableOcrBitmap);
                    ocrCanvas.drawBitmap(sLatestCleanGameBitmap, 0f, 0f, null);

                    synchronized (activeOverlayCaptureRects) {
                        for (Rect maskRect : activeOverlayCaptureRects) {
                            ocrCanvas.drawRect(maskRect, maskOverlayPaint);
                        }
                    }

                    final long currentSeq = ++outgoingFrameSeq;
                    InputImage inputImage = InputImage.fromBitmap(sReusableOcrBitmap, 0);
                    mlkitRecognizer.process(inputImage)
                            .addOnSuccessListener(visionText -> {
                                processAndTranslateDualLaneChunks(visionText, currentSeq);
                            })
                            .addOnCompleteListener(task -> {
                                isCapturingFrame = false;
                            });

                } catch (Exception e) {
                    if (img != null) {
                        try { img.close(); } catch (Exception ignored) {}
                    }
                    isCapturingFrame = false;
                }
            }
        });
    }

    private boolean isBoxOverlappingOverlayMask(Rect ocrBox) {
        int cx = ocrBox.centerX();
        int cy = ocrBox.centerY();
        synchronized (activeOverlayCaptureRects) {
            for (Rect mask : activeOverlayCaptureRects) {
                if (mask.contains(cx, cy) || Rect.intersects(mask, ocrBox)) {
                    return true;
                }
            }
        }
        return false;
    }

    private boolean hasCrispScreenUiContrast(Bitmap bmp, Rect box) {
        if (bmp == null || bmp.isRecycled()) return true;
        int x0 = Math.max(0, box.left);
        int y0 = Math.max(0, box.top);
        int x1 = Math.min(bmp.getWidth() - 1, box.right);
        int y1 = Math.min(bmp.getHeight() - 1, box.bottom);
        if (x1 <= x0 || y1 <= y0) return false;

        int stepX = Math.max(1, (x1 - x0) / 14);
        int stepY = Math.max(1, (y1 - y0) / 5);
        int minLum = 255;
        int maxLum = 0;

        for (int y = y0; y <= y1; y += stepY) {
            for (int x = x0; x <= x1; x += stepX) {
                int px = bmp.getPixel(x, y);
                int lum = (((px >> 16) & 0xFF) * 77 + ((px >> 8) & 0xFF) * 150 + (px & 0xFF) * 29) >> 8;
                if (lum < minLum) minLum = lum;
                if (lum > maxLum) maxLum = lum;
            }
        }
        return (maxLum - minLum) >= 48;
    }

    private boolean isValidCrispUiOrSubtitleText(String text, float angle, float confidence, Rect box) {
        if (text == null || text.isEmpty() || box == null) return false;
        if (isBoxOverlappingOverlayMask(box)) return false;
        if (text.matches(".*[\\u0600-\\u06FF].*")) return false;

        if (Math.abs(angle) > 4.8f) return false;
        if (confidence > 0f && confidence < 0.52f) return false;
        if (box.height() > (CAPTURE_H * 0.085)) return false;

        String onlyLetters = text.replaceAll("[^a-zA-Z]", "");
        String onlyDigits = text.replaceAll("[^0-9]", "");
        if (onlyLetters.length() < 3) {
            String upper = onlyLetters.toUpperCase();
            if (!("OK".equals(upper) || "NO".equals(upper) || "GO".equals(upper) || "ON".equals(upper) || "UP".equals(upper))) {
                return false;
            }
        }
        if (onlyDigits.length() >= onlyLetters.length()) return false;

        return hasCrispScreenUiContrast(sLatestCleanGameBitmap, box);
    }

    // تصنيف ذكي لكل قطعة نصية: هل هي "حوار سفلي في المنتصف" أم "عنصر قائمة / إشعار HUD"؟
    private String classifyTextLane(Rect box, String text) {
        double normTop = (double) box.top / CAPTURE_H;
        double normCenterX = (double) box.centerX() / CAPTURE_W;
        double normWidth = (double) box.width() / CAPTURE_W;
        int wordCount = text.trim().split("\\s+").length;

        boolean inBottomCentreZone = normTop >= 0.67
                && normCenterX >= 0.25
                && normCenterX <= 0.75;
        boolean looksLikeDialogue = wordCount >= 3 || normWidth >= 0.22;

        if (inBottomCentreZone && looksLikeDialogue) {
            return "dialogue";
        }
        return "hud";
    }

    // ===== 8. استخراج ذكي للأسطر وتقسيمها تلقائياً إلى المسار المزدوج (Dialogue + HUD) =====
    private List<DetectedUiTextChunk> extractDualLaneTextChunks(Text visionText) {
        List<DetectedUiTextChunk> rawSegments = new ArrayList<>();

        for (Text.TextBlock block : visionText.getTextBlocks()) {
            for (Text.Line line : block.getLines()) {
                Rect lineBox = line.getBoundingBox();
                if (lineBox == null) continue;
                float angle = line.getAngle();
                float lineConf = line.getConfidence();

                List<Text.Element> elements = line.getElements();
                if (elements == null || elements.isEmpty()) {
                    String t = line.getText() != null ? line.getText().trim() : "";
                    if (isValidCrispUiOrSubtitleText(t, angle, lineConf, lineBox)) {
                        rawSegments.add(new DetectedUiTextChunk(t, lineBox, 1, lineBox.height(), classifyTextLane(lineBox, t)));
                    }
                    continue;
                }

                StringBuilder segText = new StringBuilder();
                Rect segRect = null;
                Rect prevElemBox = null;
                int splitGapThreshold = Math.max(28, (int) (lineBox.height() * 2.1f));

                for (Text.Element el : elements) {
                    Rect elBox = el.getBoundingBox();
                    String elStr = el.getText() != null ? el.getText().trim() : "";
                    if (elBox == null || elStr.isEmpty()) continue;

                    if (prevElemBox != null && (elBox.left - prevElemBox.right) > splitGapThreshold) {
                        String finalized = segText.toString().trim();
                        if (segRect != null && isValidCrispUiOrSubtitleText(finalized, angle, lineConf, segRect)) {
                            rawSegments.add(new DetectedUiTextChunk(finalized, segRect, 1, segRect.height(), classifyTextLane(segRect, finalized)));
                        }
                        segText.setLength(0);
                        segRect = null;
                    }

                    if (segText.length() > 0) segText.append(' ');
                    segText.append(elStr);
                    if (segRect == null) {
                        segRect = new Rect(elBox);
                    } else {
                        segRect.union(elBox);
                    }
                    prevElemBox = elBox;
                }

                if (segText.length() > 0 && segRect != null) {
                    String finalized = segText.toString().trim();
                    if (isValidCrispUiOrSubtitleText(finalized, angle, lineConf, segRect)) {
                        rawSegments.add(new DetectedUiTextChunk(finalized, segRect, 1, segRect.height(), classifyTextLane(segRect, finalized)));
                    }
                }
            }
        }

        Collections.sort(rawSegments, new Comparator<DetectedUiTextChunk>() {
            @Override
            public int compare(DetectedUiTextChunk a, DetectedUiTextChunk b) {
                if (Math.abs(a.box.top - b.box.top) > 10) return Integer.compare(a.box.top, b.box.top);
                return Integer.compare(a.box.left, b.box.left);
            }
        });

        List<DetectedUiTextChunk> mergedChunks = new ArrayList<>();
        Set<String> seenTextAndPos = new HashSet<>();

        for (DetectedUiTextChunk seg : rawSegments) {
            String dedupKey = seg.text.toLowerCase() + "_" + (seg.box.left / 45) + "_" + (seg.box.top / 35);
            if (seenTextAndPos.contains(dedupKey)) continue;
            seenTextAndPos.add(dedupKey);

            boolean mergedIntoExisting = false;
            for (int i = mergedChunks.size() - 1; i >= 0; i--) {
                DetectedUiTextChunk prev = mergedChunks.get(i);
                if (!prev.lane.equals(seg.lane)) continue;

                int vGap = seg.box.top - prev.box.bottom;
                if (vGap < -4 || vGap > Math.max(12, prev.avgLineHeight * 0.75f)) continue;

                int heightDiff = Math.abs(seg.avgLineHeight - prev.avgLineHeight);
                if (heightDiff > Math.max(seg.avgLineHeight, prev.avgLineHeight) * 0.35f) continue;

                boolean centerAligned = Math.abs(seg.box.centerX() - prev.box.centerX()) <= 26;
                boolean leftAligned = Math.abs(seg.box.left - prev.box.left) <= 24;
                int prevWords = prev.text.split("\\s+").length;
                int currWords = seg.text.split("\\s+").length;

                boolean isDialogueParagraph = ("dialogue".equals(seg.lane) || (prevWords >= 3 && currWords >= 2 && (leftAligned || centerAligned)));
                boolean isCenteredTwoLineTitle = (centerAligned && prev.lineCount == 1 && Math.abs(seg.box.width() - prev.box.width()) < 85);

                if (isDialogueParagraph || isCenteredTwoLineTitle) {
                    prev.text = prev.text + " " + seg.text;
                    prev.box.union(seg.box);
                    prev.lineCount += 1;
                    prev.lane = classifyTextLane(prev.box, prev.text);
                    mergedIntoExisting = true;
                    break;
                }
            }

            if (!mergedIntoExisting) {
                mergedChunks.add(seg);
            }
        }

        // دمج جميع أسطر مسار الحوارات السفلية في جملة حوارية واحدة نظيفة وموزونة
        List<DetectedUiTextChunk> finalDualLaneList = new ArrayList<>();
        DetectedUiTextChunk unifiedDialogueChunk = null;

        for (DetectedUiTextChunk chunk : mergedChunks) {
            if ("dialogue".equals(chunk.lane)) {
                if (unifiedDialogueChunk == null) {
                    unifiedDialogueChunk = chunk;
                } else {
                    unifiedDialogueChunk.text = unifiedDialogueChunk.text + " " + chunk.text;
                    unifiedDialogueChunk.box.union(chunk.box);
                    unifiedDialogueChunk.lineCount += chunk.lineCount;
                }
            } else {
                finalDualLaneList.add(chunk);
            }
        }

        if (unifiedDialogueChunk != null) {
            finalDualLaneList.add(0, unifiedDialogueChunk);
        }

        return finalDualLaneList;
    }

    // ===== 8B. ترجمة فورية مباشرة على التلفزيون + مزامنة سجل الحوارات مع الجوال =====
    private String cleanArabicOutput(String rawAr) {
        if (rawAr == null) return "";
        String cleaned = rawAr
                .replaceAll("[A-Za-z0-9_|~`^<>]+", "")
                .replaceAll("\\s+([،؟!.,:])", "$1")
                .replaceAll("\\s+", " ")
                .trim();
        String onlyArabic = cleaned.replaceAll("[^\\u0600-\\u06FF]", "");
        return onlyArabic.length() >= 2 ? cleaned : "";
    }

    private String parseGoogleTranslatePayload(String rawJson) {
        if (rawJson == null || rawJson.isEmpty()) return "";
        try {
            String trimmed = rawJson.trim();
            if (trimmed.startsWith("[[[")) {
                JSONArray root = new JSONArray(trimmed);
                JSONArray sentences = root.getJSONArray(0);
                StringBuilder sb = new StringBuilder();
                for (int i = 0; i < sentences.length(); i++) {
                    JSONArray seg = sentences.getJSONArray(i);
                    if (seg.length() > 0 && !seg.isNull(0)) {
                        sb.append(seg.getString(0));
                    }
                }
                return cleanArabicOutput(sb.toString());
            } else if (trimmed.startsWith("[")) {
                JSONArray arr = new JSONArray(trimmed);
                if (arr.length() > 0) {
                    Object first = arr.get(0);
                    if (first instanceof String) {
                        return cleanArabicOutput((String) first);
                    } else if (first instanceof JSONArray) {
                        JSONArray sub = (JSONArray) first;
                        if (sub.length() > 0) {
                            return cleanArabicOutput(sub.getString(0));
                        }
                    }
                }
            }
        } catch (Exception ignored) {}
        return "";
    }

    private String fetchDirectGoogleTranslationSync(String engText) {
        if (engText == null || engText.trim().isEmpty()) return "";
        String normKey = engText.toLowerCase().replaceAll("[^a-z\\s]", "").replaceAll("\\s+", " ").trim();
        String dictHit = instantGameDictionary.get(normKey);
        if (dictHit != null) return dictHit;

        String cacheKey = engText.toLowerCase().trim();
        String cached = tvDirectTranslationCache.get(cacheKey);
        if (cached != null) return cached;

        String[] urls = new String[]{
                "https://translate.googleapis.com/translate_a/single?client=gtx&sl=en&tl=ar&dt=t&q=",
                "https://translate.googleapis.com/translate_a/t?client=dict-chrome-ex&sl=en&tl=ar&q="
        };

        for (String baseUrl : urls) {
            HttpURLConnection conn = null;
            try {
                String fullUrl = baseUrl + URLEncoder.encode(engText, "UTF-8");
                conn = (HttpURLConnection) new URL(fullUrl).openConnection();
                conn.setRequestMethod("GET");
                conn.setConnectTimeout(900);
                conn.setReadTimeout(1100);
                conn.setRequestProperty("User-Agent", "Mozilla/5.0");

                if (conn.getResponseCode() == 200) {
                    BufferedReader reader = new BufferedReader(new InputStreamReader(conn.getInputStream(), "UTF-8"));
                    StringBuilder sb = new StringBuilder();
                    String line;
                    while ((line = reader.readLine()) != null) {
                        sb.append(line);
                    }
                    reader.close();
                    String ar = parseGoogleTranslatePayload(sb.toString());
                    if (!ar.isEmpty()) {
                        if (tvDirectTranslationCache.size() > 350) {
                            tvDirectTranslationCache.clear();
                        }
                        tvDirectTranslationCache.put(cacheKey, ar);
                        return ar;
                    }
                }
            } catch (Exception ignored) {
            } finally {
                if (conn != null) conn.disconnect();
            }
        }
        return "";
    }

    private void syncDialogueLineToPhoneLog(final String arDialogue) {
        if (arDialogue == null || arDialogue.isEmpty() || arDialogue.equals(lastSyncedDialogueToPhone)) return;
        lastSyncedDialogueToPhone = arDialogue;
        if (qrAndMqttWebView == null) return;

        try {
            JSONObject msg = new JSONObject();
            msg.put("type", "DIALOGUE_LOG_SYNC");
            msg.put("sender", "tv");
            msg.put("ar", arDialogue);
            final String escapedJson = JSONObject.quote(msg.toString());
            uiHandler.post(new Runnable() {
                @Override
                public void run() {
                    if (qrAndMqttWebView != null) {
                        qrAndMqttWebView.evaluateJavascript(
                                "if(window.mqttClient && window.mqttClient.connected){ window.mqttClient.publish('siyaq/tv/sec/" + roomCode + "', " + escapedJson + "); }",
                                null
                        );
                    }
                }
            });
        } catch (Exception ignored) {}
    }

    private void processAndTranslateDualLaneChunks(Text visionText, final long frameSeq) {
        if (!isPhonePaired || !"screen".equals(currentTvSubMode) || !isScreenTranslationRunning) return;

        final List<DetectedUiTextChunk> cleanChunks = extractDualLaneTextChunks(visionText);

        if (cleanChunks.isEmpty()) {
            consecutiveEmptyDialogueFrames++;
            consecutiveEmptyHudFrames++;
            if (consecutiveEmptyDialogueFrames < 3 && consecutiveEmptyHudFrames < 3 && lastScreenItemsArray != null) {
                return;
            }
            lastPublishedOcrSignature = "EMPTY";
            uiHandler.post(new Runnable() {
                @Override
                public void run() {
                    if (frameSeq >= lastAppliedOverlaySeq) {
                        lastAppliedOverlaySeq = frameSeq;
                        lastScreenItemsArray = null;
                        renderDualLaneScreenOverlays(null, false);
                    }
                }
            });
            return;
        }

        if (!"google_gtx".equals(activeTranslatorEngine)) {
            publishDetectedScreenBlocksToPhone(cleanChunks, frameSeq);
            return;
        }

        fastDirectTranslatePool.execute(new Runnable() {
            @Override
            public void run() {
                try {
                    final int count = Math.min(cleanChunks.size(), 10);
                    final String[] arResults = new String[count];
                    final CountDownLatch latch = new CountDownLatch(count);

                    for (int i = 0; i < count; i++) {
                        final int idx = i;
                        final String en = cleanChunks.get(i).text;
                        fastDirectTranslatePool.execute(new Runnable() {
                            @Override
                            public void run() {
                                try {
                                    arResults[idx] = fetchDirectGoogleTranslationSync(en);
                                } finally {
                                    latch.countDown();
                                }
                            }
                        });
                    }

                    latch.await(1300L, TimeUnit.MILLISECONDS);

                    if (frameSeq < outgoingFrameSeq - 1) {
                        return;
                    }

                    final JSONArray overlayItems = new JSONArray();
                    for (int i = 0; i < count; i++) {
                        String ar = arResults[i];
                        if (ar == null || ar.isEmpty()) continue;

                        DetectedUiTextChunk chunk = cleanChunks.get(i);
                        Rect box = chunk.box;

                        double normX = Math.max(0.0, Math.min(0.98, (double) box.left / CAPTURE_W));
                        double normY = Math.max(0.0, Math.min(0.98, (double) box.top / CAPTURE_H));
                        double normW = Math.max(0.03, Math.min(1.0 - normX, (double) box.width() / CAPTURE_W));
                        double normH = Math.max(0.022, Math.min(1.0 - normY, (double) box.height() / CAPTURE_H));

                        JSONObject item = new JSONObject();
                        item.put("id", chunk.lane + "_" + Math.round(normX * 18) + "_" + Math.round(normY * 18) + "_" + i);
                        item.put("lane", chunk.lane);
                        item.put("en", chunk.text);
                        item.put("ar", ar);
                        item.put("x", normX);
                        item.put("y", normY);
                        item.put("w", normW);
                        item.put("h", normH);
                        item.put("lineCount", chunk.lineCount);
                        item.put("lineH", (double) chunk.avgLineHeight / CAPTURE_H);
                        overlayItems.put(item);
                    }

                    if (overlayItems.length() > 0) {
                        uiHandler.post(new Runnable() {
                            @Override
                            public void run() {
                                if (!isScreenTranslationRunning || !"screen".equals(currentTvSubMode)) return;
                                if (frameSeq >= lastAppliedOverlaySeq) {
                                    lastAppliedOverlaySeq = frameSeq;
                                    lastScreenItemsArray = overlayItems;
                                    renderDualLaneScreenOverlays(overlayItems, false);
                                }
                            }
                        });
                    }
                } catch (Exception ignored) {}
            }
        });
    }

    private void publishDetectedScreenBlocksToPhone(List<DetectedUiTextChunk> cleanChunks, long frameSeq) {
        if (!isPhonePaired || !"screen".equals(currentTvSubMode) || qrAndMqttWebView == null) return;
        try {
            JSONArray blocksArray = new JSONArray();
            StringBuilder sigBuilder = new StringBuilder();
            int idx = 0;

            for (DetectedUiTextChunk chunk : cleanChunks) {
                if (idx >= 10) break;
                Rect box = chunk.box;

                double normX = Math.max(0.0, Math.min(0.98, (double) box.left / CAPTURE_W));
                double normY = Math.max(0.0, Math.min(0.98, (double) box.top / CAPTURE_H));
                double normW = Math.max(0.03, Math.min(1.0 - normX, (double) box.width() / CAPTURE_W));
                double normH = Math.max(0.022, Math.min(1.0 - normY, (double) box.height() / CAPTURE_H));

                JSONObject bObj = new JSONObject();
                bObj.put("id", chunk.lane + "_" + Math.round(normX * 18) + "_" + Math.round(normY * 18) + "_" + idx);
                bObj.put("lane", chunk.lane);
                bObj.put("text", chunk.text);
                bObj.put("x", normX);
                bObj.put("y", normY);
                bObj.put("w", normW);
                bObj.put("h", normH);
                bObj.put("lineCount", chunk.lineCount);
                bObj.put("lineH", (double) chunk.avgLineHeight / CAPTURE_H);
                blocksArray.put(bObj);

                String onlyLetters = chunk.text.replaceAll("[^a-zA-Z]", "").toLowerCase();
                sigBuilder.append(chunk.lane)
                        .append(':')
                        .append(onlyLetters)
                        .append('@')
                        .append(Math.round(normX * 16))
                        .append(':')
                        .append(Math.round(normY * 16))
                        .append('|');
                idx++;
            }

            String currentSig = blocksArray.length() == 0 ? "EMPTY" : sigBuilder.toString();
            long now = System.currentTimeMillis();

            if (currentSig.equals(lastPublishedOcrSignature)) {
                if ("EMPTY".equals(currentSig) || (now - lastPublishedOcrTime) < 3500L) {
                    return;
                }
            }
            lastPublishedOcrSignature = currentSig;
            lastPublishedOcrTime = now;

            JSONObject payload = new JSONObject();
            payload.put("type", "SCREEN_TEXTS_BATCH");
            payload.put("sender", "tv");
            payload.put("frameId", now);
            payload.put("frameSeq", frameSeq);
            payload.put("screenWidth", CAPTURE_W);
            payload.put("screenHeight", CAPTURE_H);
            payload.put("blocks", blocksArray);

            final String escapedJson = JSONObject.quote(payload.toString());
            uiHandler.post(new Runnable() {
                @Override
                public void run() {
                    if (qrAndMqttWebView != null) {
                        qrAndMqttWebView.evaluateJavascript(
                                "if(window.mqttClient && window.mqttClient.connected){ window.mqttClient.publish('siyaq/tv/sec/" + roomCode + "', " + escapedJson + "); }",
                                null
                        );
                    }
                }
            });
        } catch (Exception ignored) {}
    }

    private BitmapDrawable buildTruePixelatedCamouflage(Bitmap gameBitmap, double normX, double normY, double normW, double normH) {
        try {
            if (gameBitmap == null || gameBitmap.isRecycled()) return null;

            int bmpW = gameBitmap.getWidth();
            int bmpH = gameBitmap.getHeight();

            int safeX = Math.max(0, Math.min(bmpW - 4, (int) Math.round(normX * bmpW)));
            int safeY = Math.max(0, Math.min(bmpH - 4, (int) Math.round(normY * bmpH)));
            int safeW = Math.max(8, Math.min(bmpW - safeX, (int) Math.round(normW * bmpW)));
            int safeH = Math.max(8, Math.min(bmpH - safeY, (int) Math.round(normH * bmpH)));

            int borderR = 0, borderG = 0, borderB = 0, borderCount = 0;
            int stepX = Math.max(4, safeW / 8);
            int topSampleY = Math.max(0, safeY - 2);
            int botSampleY = Math.min(bmpH - 1, safeY + safeH + 1);

            for (int sx = safeX; sx < safeX + safeW; sx += stepX) {
                int pTop = gameBitmap.getPixel(sx, topSampleY);
                int pBot = gameBitmap.getPixel(sx, botSampleY);
                borderR += Color.red(pTop) + Color.red(pBot);
                borderG += Color.green(pTop) + Color.green(pBot);
                borderB += Color.blue(pTop) + Color.blue(pBot);
                borderCount += 2;
            }

            int baseR = borderCount > 0 ? borderR / borderCount : 24;
            int baseG = borderCount > 0 ? borderG / borderCount : 28;
            int baseB = borderCount > 0 ? borderB / borderCount : 38;

            Bitmap mosaicBitmap = Bitmap.createBitmap(safeW, safeH, Bitmap.Config.ARGB_8888);
            Canvas canvas = new Canvas(mosaicBitmap);
            Paint blockPaint = new Paint();
            blockPaint.setStyle(Paint.Style.FILL);
            blockPaint.setAntiAlias(false);

            int blockSize = Math.max(8, PIXEL_BLOCK_SIZE);
            for (int by = 0; by < safeH; by += blockSize) {
                for (int bx = 0; bx < safeW; bx += blockSize) {
                    int sampleX = Math.min(bmpW - 1, safeX + bx + (blockSize / 2));
                    int sampleY = Math.min(bmpH - 1, safeY + by + (blockSize / 2));
                    int px = gameBitmap.getPixel(sampleX, sampleY);
                    int r = (Color.red(px) * 60 + baseR * 40) / 100;
                    int g = (Color.green(px) * 60 + baseG * 40) / 100;
                    int b = (Color.blue(px) * 60 + baseB * 40) / 100;

                    blockPaint.setColor(Color.argb(255, (int) (r * 0.85f), (int) (g * 0.85f), (int) (b * 0.85f)));
                    canvas.drawRect(bx, by, Math.min(safeW, bx + blockSize), Math.min(safeH, by + blockSize), blockPaint);
                }
            }

            BitmapDrawable drawable = new BitmapDrawable(getResources(), mosaicBitmap);
            drawable.setFilterBitmap(false);
            return drawable;
        } catch (Exception e) {
            return null;
        }
    }

    private void ensureOverlayStageCreated() {
        if (fullScreenOverlayStage != null) return;

        windowManager = (WindowManager) getSystemService(WINDOW_SERVICE);

        fullScreenOverlayStage = new FrameLayout(this);
        fullScreenOverlayStage.setLayoutDirection(View.LAYOUT_DIRECTION_LTR);
        fullScreenOverlayStage.setBackgroundColor(Color.TRANSPARENT);

        // 1. حاوية بطاقات القوائم والإشعارات المستقلة (HUD Cards)
        screenItemsOverlayLayer = new FrameLayout(this);
        screenItemsOverlayLayer.setLayoutDirection(View.LAYOUT_DIRECTION_LTR);
        screenItemsOverlayLayer.setBackgroundColor(Color.TRANSPARENT);
        fullScreenOverlayStage.addView(screenItemsOverlayLayer, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.MATCH_PARENT
        ));

        // 2. شريط الحوارات السفلية الموحّد في وضع الشاشة (مستقل تماماً عن القوائم)
        screenDialogueBannerBox = new FrameLayout(this);
        screenDialogueBannerBox.setLayoutDirection(View.LAYOUT_DIRECTION_LTR);
        screenDialogueBg = new GradientDrawable();
        screenDialogueBg.setShape(GradientDrawable.RECTANGLE);
        screenDialogueBg.setColor(Color.argb(222, 0, 0, 0));
        screenDialogueBg.setCornerRadius(6f);
        screenDialogueBannerBox.setBackground(screenDialogueBg);
        screenDialogueBannerBox.setPadding(24, 10, 24, 10);
        screenDialogueBannerBox.setVisibility(View.GONE);

        screenDialogueTextView = new TextView(this);
        screenDialogueTextView.setText("");
        screenDialogueTextView.setTextColor(Color.WHITE);
        screenDialogueTextView.setTextSize(TypedValue.COMPLEX_UNIT_SP, 26);
        screenDialogueTextView.setTypeface(resolveRequestedArabicTypeface("Tajawal", true));
        screenDialogueTextView.setGravity(Gravity.CENTER);
        screenDialogueTextView.setTextDirection(View.TEXT_DIRECTION_RTL);
        screenDialogueTextView.setIncludeFontPadding(false);
        screenDialogueTextView.setMaxWidth((int) (realScreenW * 0.84f));
        screenDialogueTextView.getPaint().setFakeBoldText(true);
        screenDialogueTextView.setShadowLayer(4f, 0f, 2f, Color.argb(245, 0, 0, 0));

        screenDialogueBannerBox.addView(screenDialogueTextView, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.WRAP_CONTENT,
                FrameLayout.LayoutParams.WRAP_CONTENT,
                Gravity.CENTER));

        fullScreenOverlayStage.addView(screenDialogueBannerBox, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.WRAP_CONTENT,
                FrameLayout.LayoutParams.WRAP_CONTENT,
                Gravity.TOP | Gravity.LEFT));

        // 3. شريط ترجمة وضع الكاميرا
        subtitleBannerBox = new FrameLayout(this);
        subtitleBannerBox.setLayoutDirection(View.LAYOUT_DIRECTION_LTR);
        boxBackground = new GradientDrawable();
        boxBackground.setShape(GradientDrawable.RECTANGLE);
        boxBackground.setColor(Color.argb(217, 0, 0, 0));
        boxBackground.setCornerRadius(0f);
        boxBackground.setStroke(0, Color.TRANSPARENT);
        subtitleBannerBox.setBackground(boxBackground);
        subtitleBannerBox.setPadding(24, 12, 24, 12);
        subtitleBannerBox.setVisibility(View.GONE);

        subtitleTextView = new TextView(this);
        subtitleTextView.setText("");
        subtitleTextView.setTextColor(Color.WHITE);
        subtitleTextView.setAlpha(1.0f);
        subtitleTextView.setTextSize(TypedValue.COMPLEX_UNIT_SP, 26);
        subtitleTextView.setTypeface(resolveRequestedArabicTypeface("IBM Plex Sans Arabic", true));
        subtitleTextView.setGravity(Gravity.CENTER);
        subtitleTextView.setTextDirection(View.TEXT_DIRECTION_RTL);
        subtitleTextView.setIncludeFontPadding(false);
        subtitleTextView.setMaxWidth((int) (realScreenW * 0.85f));

        subtitleTextView.setPaintFlags(subtitleTextView.getPaintFlags()
                | Paint.ANTI_ALIAS_FLAG
                | Paint.SUBPIXEL_TEXT_FLAG
                | Paint.LINEAR_TEXT_FLAG);
        subtitleTextView.getPaint().setFakeBoldText(true);
        subtitleTextView.setShadowLayer(4.5f, 0f, 2f, Color.argb(240, 0, 0, 0));

        subtitleBannerBox.addView(subtitleTextView, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.WRAP_CONTENT,
                FrameLayout.LayoutParams.WRAP_CONTENT,
                Gravity.CENTER));

        FrameLayout.LayoutParams bannerLp = new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.WRAP_CONTENT,
                FrameLayout.LayoutParams.WRAP_CONTENT,
                Gravity.TOP | Gravity.LEFT);
        fullScreenOverlayStage.addView(subtitleBannerBox, bannerLp);

        int layoutFlag;
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            layoutFlag = canDrawOverlaySafely()
                    ? WindowManager.LayoutParams.TYPE_APPLICATION_OVERLAY
                    : WindowManager.LayoutParams.TYPE_APPLICATION_PANEL;
        } else {
            layoutFlag = WindowManager.LayoutParams.TYPE_PHONE;
        }

        stageWindowParams = new WindowManager.LayoutParams(
                WindowManager.LayoutParams.MATCH_PARENT,
                WindowManager.LayoutParams.MATCH_PARENT,
                layoutFlag,
                WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE
                        | WindowManager.LayoutParams.FLAG_NOT_TOUCHABLE
                        | WindowManager.LayoutParams.FLAG_LAYOUT_IN_SCREEN
                        | WindowManager.LayoutParams.FLAG_HARDWARE_ACCELERATED,
                PixelFormat.TRANSLUCENT);

        stageWindowParams.gravity = Gravity.TOP | Gravity.LEFT;
        try {
            windowManager.addView(fullScreenOverlayStage, stageWindowParams);
        } catch (Exception ignored) {}
    }

    // ===== 10. عرض المسار المزدوج بتثبيت البطاقات مكانياً (Sticky View Cache) دون وميض =====
    private boolean collidesWithAnyRect(Rect candidate, List<Rect> rectList, int skipIdx) {
        for (int j = 0; j < rectList.size(); j++) {
            if (j == skipIdx) continue;
            if (Rect.intersects(candidate, rectList.get(j))) {
                return true;
            }
        }
        return false;
    }

    private Rect toCaptureMaskRect(int pxX, int pxY, int pxW, int pxH) {
        int maskLeft = Math.max(0, (int) Math.floor(((double) pxX / realScreenW) * CAPTURE_W) - 4);
        int maskTop = Math.max(0, (int) Math.floor(((double) pxY / realScreenH) * CAPTURE_H) - 4);
        int maskRight = Math.min(CAPTURE_W, (int) Math.ceil(((double) (pxX + pxW) / realScreenW) * CAPTURE_W) + 4);
        int maskBottom = Math.min(CAPTURE_H, (int) Math.ceil(((double) (pxY + pxH) / realScreenH) * CAPTURE_H) + 4);
        return new Rect(maskLeft, maskTop, maskRight, maskBottom);
    }

    private void renderDualLaneScreenOverlays(JSONArray items, boolean forceStyleRefresh) {
        if (screenItemsOverlayLayer == null || screenDialogueBannerBox == null) return;
        if (subtitleBannerBox != null) subtitleBannerBox.setVisibility(View.GONE);

        String fontFamilyRaw = lastStyleJson != null ? lastStyleJson.optString("fontFamily", "Tajawal") : "Tajawal";
        boolean isBold = lastStyleJson == null || lastStyleJson.optBoolean("isBold", true);
        String textColorStr = lastStyleJson != null ? lastStyleJson.optString("textColor", "#FFFFFF") : "#FFFFFF";
        int textOpacity = lastStyleJson != null ? lastStyleJson.optInt("textOpacity", 100) : 100;
        String bgColorStr = lastStyleJson != null ? lastStyleJson.optString("bgColor", "#000000") : "#000000";
        int bgOpacity = lastStyleJson != null ? lastStyleJson.optInt("bgOpacity", 85) : 85;
        boolean useCamouflage = lastStyleJson != null && lastStyleJson.optBoolean("camouflageBlurMode", false);

        int parsedTextCol;
        try { parsedTextCol = Color.parseColor(textColorStr); } catch (Exception e) { parsedTextCol = Color.WHITE; }
        int textAlpha = textOpacity >= 99 ? 255 : Math.max(40, Math.min(255, Math.round(textOpacity * 2.55f)));
        int finalTextColor = Color.argb(textAlpha, Color.red(parsedTextCol), Color.green(parsedTextCol), Color.blue(parsedTextCol));

        int parsedBg;
        try { parsedBg = Color.parseColor(bgColorStr); } catch (Exception e) { parsedBg = Color.BLACK; }
        int solidBgAlpha = Math.max(0, Math.min(255, Math.round(bgOpacity * 2.55f)));
        int finalBgColor = Color.argb(solidBgAlpha, Color.red(parsedBg), Color.green(parsedBg), Color.blue(parsedBg));
        Typeface tf = resolveRequestedArabicTypeface(fontFamilyRaw, isBold);

        JSONObject dialogueItem = null;
        List<JSONObject> hudItems = new ArrayList<>();
        List<Rect> allOriginalScreenRects = new ArrayList<>();

        if (items != null) {
            for (int i = 0; i < items.length(); i++) {
                JSONObject it = items.optJSONObject(i);
                if (it == null) continue;
                String ar = it.optString("ar", "").trim();
                if (ar.isEmpty()) continue;

                double nx = it.optDouble("x", 0.1);
                double ny = it.optDouble("y", 0.5);
                double nw = it.optDouble("w", 0.2);
                double nh = it.optDouble("h", 0.04);

                String lane = it.optString("lane", "");
                if (lane.isEmpty()) {
                    lane = (ny >= 0.67 && nx >= 0.12 && (nx + nw) <= 0.88) ? "dialogue" : "hud";
                }

                if ("dialogue".equals(lane) && dialogueItem == null) {
                    dialogueItem = it;
                } else {
                    hudItems.add(it);
                    int ox = (int) Math.round(nx * realScreenW);
                    int oy = (int) Math.round(ny * realScreenH);
                    int ow = Math.max(40, (int) Math.round(nw * realScreenW));
                    int oh = Math.max(20, (int) Math.round(nh * realScreenH));
                    allOriginalScreenRects.add(new Rect(ox - 2, oy - 2, ox + ow + 2, oy + oh + 2));
                }
            }
        }

        List<Rect> nextCaptureMasks = new ArrayList<>();
        List<Rect> occupiedScreenRects = new ArrayList<>();

        // ===== المسار 1: شريط الحوارات السفلية الموحّد والمستقل =====
        if (dialogueItem != null) {
            consecutiveEmptyDialogueFrames = 0;
            String dialogueAr = dialogueItem.optString("ar", "").trim();
            double origTopNorm = dialogueItem.optDouble("y", 0.82);

            screenDialogueTextView.setText(dialogueAr);
            screenDialogueTextView.setTextColor(finalTextColor);
            screenDialogueTextView.setTypeface(tf);
            screenDialogueTextView.getPaint().setFakeBoldText(isBold);
            int fontSizeSp = lastStyleJson != null ? lastStyleJson.optInt("fontSize", 24) : 24;
            screenDialogueTextView.setTextSize(TypedValue.COMPLEX_UNIT_SP, Math.max(20, Math.min(34, fontSizeSp * 1.12f)));

            screenDialogueBg.setColor(finalBgColor);
            screenDialogueBannerBox.setBackground(screenDialogueBg);
            screenDialogueBannerBox.setVisibility(View.VISIBLE);

            int specW = View.MeasureSpec.makeMeasureSpec(realScreenW, View.MeasureSpec.AT_MOST);
            int specH = View.MeasureSpec.makeMeasureSpec(realScreenH, View.MeasureSpec.AT_MOST);
            screenDialogueBannerBox.measure(specW, specH);
            int boxW = screenDialogueBannerBox.getMeasuredWidth();
            int boxH = screenDialogueBannerBox.getMeasuredHeight();

            // وضع شريط الحوار فوق الحوار الأصلي مباشرة حتى لا يغطيه
            int origTopPx = (int) Math.round(origTopNorm * realScreenH);
            int targetX = Math.max(16, (realScreenW - boxW) / 2);
            int targetY = Math.max(24, origTopPx - boxH - 10);

            screenDialogueBannerBox.setTranslationX(targetX);
            screenDialogueBannerBox.setTranslationY(targetY);

            Rect dialogueRect = new Rect(targetX, targetY, targetX + boxW, targetY + boxH);
            occupiedScreenRects.add(dialogueRect);
            nextCaptureMasks.add(toCaptureMaskRect(targetX, targetY, boxW, boxH));
            syncDialogueLineToPhoneLog(dialogueAr);
        } else {
            consecutiveEmptyDialogueFrames++;
            if (consecutiveEmptyDialogueFrames >= 2 || items == null) {
                screenDialogueBannerBox.setVisibility(View.GONE);
                screenDialogueTextView.setText("");
            } else if (screenDialogueBannerBox.getVisibility() == View.VISIBLE) {
                int w = screenDialogueBannerBox.getMeasuredWidth();
                int h = screenDialogueBannerBox.getMeasuredHeight();
                int x = (int) screenDialogueBannerBox.getTranslationX();
                int y = (int) screenDialogueBannerBox.getTranslationY();
                occupiedScreenRects.add(new Rect(x, y, x + w, y + h));
                nextCaptureMasks.add(toCaptureMaskRect(x, y, w, h));
            }
        }

        // ===== المسار 2: بطاقات القوائم والإشعارات المثبتة مكانياً (Sticky HUD Cards) =====
        TextPaint measurePaint = new TextPaint(Paint.ANTI_ALIAS_FLAG);
        measurePaint.setTypeface(tf);
        measurePaint.setFakeBoldText(isBold);

        Set<String> activeKeysThisFrame = new HashSet<>();
        int halfScreenY = realScreenH / 2;

        if (!hudItems.isEmpty()) {
            consecutiveEmptyHudFrames = 0;
        } else {
            consecutiveEmptyHudFrames++;
        }

        for (int i = 0; i < hudItems.size(); i++) {
            JSONObject item = hudItems.get(i);
            String arText = item.optString("ar", "").trim();
            double nx = item.optDouble("x", 0.1);
            double ny = item.optDouble("y", 0.5);
            double nw = item.optDouble("w", 0.2);
            double nh = item.optDouble("h", 0.04);

            String stickyKey = arText + "_" + Math.round(nx * 14) + "_" + Math.round(ny * 14);
            activeKeysThisFrame.add(stickyKey);

            // إذا كانت البطاقة معروضة مسبقاً في نفس مكانها، نثبتها تماماً بدون إعادة إنشاء أو تحريك
            StickyHudCard existingCard = stickyHudCardMap.get(stickyKey);
            if (existingCard != null && !forceStyleRefresh && !useCamouflage) {
                existingCard.missedFrames = 0;
                occupiedScreenRects.add(existingCard.screenRect);
                nextCaptureMasks.add(existingCard.captureMaskRect);
                continue;
            }

            int origX = (int) Math.round(nx * realScreenW);
            int origY = (int) Math.round(ny * realScreenH);
            int origW = Math.max(44, (int) Math.round(nw * realScreenW));
            int origH = Math.max(22, (int) Math.round(nh * realScreenH));
            int origCenterX = origX + (origW / 2);
            int origCenterY = origY + (origH / 2);

            int lineCount = Math.max(1, item.optInt("lineCount", 1));
            double normLineH = item.optDouble("lineH", nh / lineCount);
            int singleLineOrigPx = Math.max(20, (int) Math.round(normLineH * realScreenH));

            float exactTextSizePx = Math.max(17f, Math.min(42f, singleLineOrigPx * 0.85f));
            measurePaint.setTextSize(exactTextSizePx);

            float rawMeasuredArWidth = measurePaint.measureText(arText);
            int padH = 11;
            int padV = 4;

            int pxW;
            int pxH;
            if (lineCount > 1 || rawMeasuredArWidth > origW * 1.45f) {
                int targetLines = Math.max(lineCount, (int) Math.ceil(rawMeasuredArWidth / Math.max(150f, origW * 1.15f)));
                targetLines = Math.min(4, targetLines);
                pxW = Math.min(realScreenW - 24, Math.max(origW, (int) Math.ceil(rawMeasuredArWidth / targetLines) + (padH * 2)));
                pxH = Math.max(origH, Math.round(targetLines * (exactTextSizePx * 1.30f)) + (padV * 2));
            } else {
                pxW = Math.min(realScreenW - 24, Math.max(54, (int) Math.ceil(rawMeasuredArWidth) + (padH * 2)));
                pxH = Math.max(28, Math.round(singleLineOrigPx * 1.15f) + (padV * 2));
            }

            int centeredX = Math.max(12, Math.min(realScreenW - pxW - 12, origCenterX - (pxW / 2)));
            int aboveY = Math.max(6, origY - pxH - 4);
            int belowY = Math.min(realScreenH - pxH - 6, origY + origH + 4);

            int pxX = centeredX;
            int pxY;

            if (useCamouflage) {
                pxY = Math.max(6, Math.min(realScreenH - pxH - 6, origY));
            } else {
                int preferredY = (origCenterY >= halfScreenY) ? aboveY : belowY;
                int alternateY = (origCenterY >= halfScreenY) ? belowY : aboveY;

                Rect prefRect = new Rect(pxX, preferredY, pxX + pxW, preferredY + pxH);
                Rect altRect = new Rect(pxX, alternateY, pxX + pxW, alternateY + pxH);

                if (!collidesWithAnyRect(prefRect, allOriginalScreenRects, i)
                        && !collidesWithAnyRect(prefRect, occupiedScreenRects, -1)) {
                    pxY = preferredY;
                } else if (!collidesWithAnyRect(altRect, allOriginalScreenRects, i)
                        && !collidesWithAnyRect(altRect, occupiedScreenRects, -1)) {
                    pxY = alternateY;
                } else {
                    int rightX = origX + origW + 10;
                    int leftX = origX - pxW - 10;
                    int sideY = Math.max(6, Math.min(realScreenH - pxH - 6, origCenterY - (pxH / 2)));
                    Rect rightRect = new Rect(rightX, sideY, rightX + pxW, sideY + pxH);
                    Rect leftRect = new Rect(leftX, sideY, leftX + pxW, sideY + pxH);

                    if (rightX + pxW <= realScreenW - 8
                            && !collidesWithAnyRect(rightRect, allOriginalScreenRects, i)
                            && !collidesWithAnyRect(rightRect, occupiedScreenRects, -1)) {
                        pxX = rightX;
                        pxY = sideY;
                    } else if (leftX >= 8
                            && !collidesWithAnyRect(leftRect, allOriginalScreenRects, i)
                            && !collidesWithAnyRect(leftRect, occupiedScreenRects, -1)) {
                        pxX = leftX;
                        pxY = sideY;
                    } else {
                        pxY = preferredY;
                    }
                }
            }

            if (existingCard != null && existingCard.view != null) {
                screenItemsOverlayLayer.removeView(existingCard.view);
            }

            TextView tv = new TextView(this);
            tv.setText(arText);
            tv.setTextColor(finalTextColor);
            tv.setTypeface(tf);
            tv.getPaint().setFakeBoldText(isBold);
            tv.setGravity(Gravity.CENTER);
            tv.setTextDirection(View.TEXT_DIRECTION_RTL);
            tv.setIncludeFontPadding(false);
            tv.setPadding(padH, padV, padH, padV);
            tv.setTextSize(TypedValue.COMPLEX_UNIT_PX, exactTextSizePx);
            tv.setShadowLayer(3.5f, 0f, 1.5f, Color.argb(245, 0, 0, 0));

            if (useCamouflage && sLatestCleanGameBitmap != null) {
                BitmapDrawable pixelPatch = buildTruePixelatedCamouflage(sLatestCleanGameBitmap, nx, ny, nw, nh);
                if (pixelPatch != null) {
                    tv.setBackground(pixelPatch);
                } else {
                    tv.setBackgroundColor(Color.argb(245, 20, 24, 34));
                }
            } else {
                GradientDrawable customBg = new GradientDrawable();
                customBg.setColor(finalBgColor);
                customBg.setCornerRadius(5f);
                tv.setBackground(customBg);
            }

            FrameLayout.LayoutParams lp = new FrameLayout.LayoutParams(pxW, pxH, Gravity.TOP | Gravity.LEFT);
            lp.leftMargin = pxX;
            lp.topMargin = pxY;
            screenItemsOverlayLayer.addView(tv, lp);

            Rect screenRect = new Rect(pxX, pxY, pxX + pxW, pxY + pxH);
            Rect maskRect = toCaptureMaskRect(pxX, pxY, pxW, pxH);
            stickyHudCardMap.put(stickyKey, new StickyHudCard(stickyKey, arText, tv, screenRect, maskRect));
            occupiedScreenRects.add(screenRect);
            nextCaptureMasks.add(maskRect);
        }

        // إزالة البطاقات التي اختفت نصوصها فعلياً من الشاشة فقط (بعد 2 إطارات متتالية)
        Iterator> it = stickyHudCardMap.entrySet().iterator();
        while (it.hasNext()) {
            Map.Entry<String, StickyHudCard> entry = it.next();
            if (!activeKeysThisFrame.contains(entry.getKey())) {
                StickyHudCard card = entry.getValue();
                card.missedFrames++;
                if (items == null || card.missedFrames >= 2) {
                    if (card.view != null) {
                        screenItemsOverlayLayer.removeView(card.view);
                    }
                    it.remove();
                } else {
                    nextCaptureMasks.add(card.captureMaskRect);
                }
            }
        }

        synchronized (activeOverlayCaptureRects) {
            activeOverlayCaptureRects.clear();
            activeOverlayCaptureRects.addAll(nextCaptureMasks);
        }
    }

    private void positionBannerAccurately(View bannerView, float normCenterX, float normCenterY) {
        if (bannerView == null) return;

        int specW = View.MeasureSpec.makeMeasureSpec(realScreenW, View.MeasureSpec.AT_MOST);
        int specH = View.MeasureSpec.makeMeasureSpec(realScreenH, View.MeasureSpec.AT_MOST);
        bannerView.measure(specW, specH);

        int boxW = bannerView.getMeasuredWidth();
        int boxH = bannerView.getMeasuredHeight();

        float centerX = realScreenW * normCenterX;
        float centerY = realScreenH * normCenterY;

        float targetX = Math.max(0f, Math.min(realScreenW - boxW, centerX - (boxW / 2f)));
        float targetY = Math.max(0f, Math.min(realScreenH - boxH, centerY - (boxH / 2f)));

        bannerView.setTranslationX(targetX);
        bannerView.setTranslationY(targetY);
    }

    private void applySmoothHardwareSubtitleStyle(JSONObject style) {
        if (fullScreenOverlayStage == null || subtitleBannerBox == null || subtitleTextView == null) return;
        try {
            DisplayMetrics dm = getResources().getDisplayMetrics();

            String fontFamilyRaw = style.optString("fontFamily", "IBM Plex Sans Arabic");
            boolean isBold = style.optBoolean("isBold", true);
            Typeface resolvedTf = resolveRequestedArabicTypeface(fontFamilyRaw, isBold);
            subtitleTextView.setTypeface(resolvedTf);
            subtitleTextView.getPaint().setFakeBoldText(isBold);

            int fontSize = style.optInt("fontSize", 24);
            subtitleTextView.setTextSize(TypedValue.COMPLEX_UNIT_SP, fontSize * 1.22f);

            String textColorStr = style.optString("textColor", "#FFFFFF");
            int textOpacity = style.optInt("textOpacity", 100);
            int parsedTextCol = Color.parseColor(textColorStr);
            int textAlpha = textOpacity >= 99 ? 255 : Math.max(40, Math.min(255, Math.round(textOpacity * 2.55f)));
            subtitleTextView.setAlpha(1.0f);
            subtitleTextView.setTextColor(Color.argb(
                    textAlpha,
                    Color.red(parsedTextCol),
                    Color.green(parsedTextCol),
                    Color.blue(parsedTextCol)
            ));

            String bgColorStr = style.optString("bgColor", "#000000");
            int bgOpacity = style.optInt("bgOpacity", 85);
            int parsedBgCol;
            try { parsedBgCol = Color.parseColor(bgColorStr); } catch (Exception e) { parsedBgCol = Color.BLACK; }
            int bgAlpha = Math.max(0, Math.min(255, Math.round(bgOpacity * 2.55f)));

            boxBackground.setCornerRadius(0f);
            boxBackground.setStroke(0, Color.TRANSPARENT);
            boxBackground.setColor(Color.argb(
                    bgAlpha,
                    Color.red(parsedBgCol),
                    Color.green(parsedBgCol),
                    Color.blue(parsedBgCol)
            ));
            subtitleBannerBox.setBackground(boxBackground);

            int bgWidthPct = Math.max(25, Math.min(100, style.optInt("bgWidth", 92)));
            int bgHeightPx = Math.max(4, Math.min(32, style.optInt("bgHeight", 10)));
            int maxWidthPx = (int) (realScreenW * (bgWidthPct / 100f));
            subtitleTextView.setMaxWidth(maxWidthPx);

            int padV = (int) (bgHeightPx * dm.density);
            int padH = (int) (Math.max(10, Math.round(bgHeightPx * 1.5f)) * dm.density);
            subtitleBannerBox.setPadding(padH, padV, padH, padV);

            int posX = Math.max(10, Math.min(90, style.optInt("posX", 50)));
            int posY = Math.max(10, Math.min(92, style.optInt("posY", 82)));
            positionBannerAccurately(subtitleBannerBox, posX / 100f, posY / 100f);
        } catch (Exception ignored) {}
    }

    private void rotateToFreshRoomCode() {
        roomCode = generateRandomRoomCode();
        if (codeView != null) {
            codeView.setText(roomCode);
        }
        loadQrAndWaitBridge();
    }

    private void performCleanUnpairAndRotateCode() {
        isPhonePaired = false;
        stopScreenBroadcastCompletely();
        if (qrAndMqttWebView != null) {
            qrAndMqttWebView.evaluateJavascript(
                    "if(window.mqttClient && window.mqttClient.connected){ window.mqttClient.publish('siyaq/tv/sec/" + roomCode + "', JSON.stringify({type:'UNPAIRED', sender:'tv'})); }",
                    null);
        }
        hideOverlayStage();
        updateUiForPairingState(false);
        uiHandler.postDelayed(new Runnable() {
            @Override
            public void run() {
                rotateToFreshRoomCode();
            }
        }, 180);
        Toast.makeText(this, isArabic ? "تم إلغاء الاقتران وإيقاف البث ✓" : "Unpaired & Broadcast Stopped ✓", Toast.LENGTH_SHORT).show();
    }

    private void hideOverlayStage() {
        clearAllStickyHudCards();
        lastScreenItemsArray = null;
        if (fullScreenOverlayStage != null && windowManager != null) {
            try {
                windowManager.removeView(fullScreenOverlayStage);
            } catch (Exception ignored) {}
            fullScreenOverlayStage = null;
            screenItemsOverlayLayer = null;
            screenDialogueBannerBox = null;
            screenDialogueTextView = null;
            subtitleBannerBox = null;
            subtitleTextView = null;
        }
    }

    private void releaseScreenCaptureResources() {
        try {
            if (sVirtualDisplay != null) {
                sVirtualDisplay.release();
                sVirtualDisplay = null;
            }
            if (sImageReader != null) {
                sImageReader.close();
                sImageReader = null;
            }
            if (sMediaProjection != null) {
                sMediaProjection.stop();
                sMediaProjection = null;
            }
        } catch (Exception ignored) {}
    }

    private void updateUiForPairingState(boolean paired) {
        if (paired) {
            String modeAr = "screen".equals(currentTvSubMode) ? " (وضع الشاشة)" : " (وضع الكاميرا)";
            String modeEn = "screen".equals(currentTvSubMode) ? " (Screen Mode)" : " (Camera Mode)";
            statusBadge.setText(isArabic ? "● متصل بالجوال" + modeAr : "● Phone Connected" + modeEn);
            statusBadge.setTextColor(Color.parseColor(COLOR_ACCENT));
        } else {
            statusBadge.setText(isArabic ? "غير متصل" : "Not Connected");
            statusBadge.setTextColor(Color.parseColor(COLOR_TEXT_SOFT));
        }
    }

    @Override
    protected void onDestroy() {
        super.onDestroy();
        fontDownloadExecutor.shutdownNow();
        fastDirectTranslatePool.shutdownNow();
        uiHandler.removeCallbacks(keepAliveRunnable);
        uiHandler.removeCallbacks(screenOcrLoopRunnable);
        if (!isPhonePaired) {
            stopScreenBroadcastCompletely();
        }
        if (ocrBackgroundThread != null) {
            try {
                ocrBackgroundThread.quitSafely();
            } catch (Exception ignored) {}
        }
        if (wakeLock != null && wakeLock.isHeld()) {
            try {
                wakeLock.release();
            } catch (Exception ignored) {}
        }
        hideOverlayStage();
        if (qrAndMqttWebView != null) {
            qrAndMqttWebView.destroy();
        }
    }
}
