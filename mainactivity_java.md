package com.siyaq.tv;

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
import android.os.IBinder;
import android.os.Looper;
import android.os.PowerManager;
import android.provider.Settings;
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

import java.io.File;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.net.HttpURLConnection;
import java.net.URL;
import java.nio.ByteBuffer;
import java.util.HashMap;
import java.util.Map;
import java.util.Random;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

public class MainActivity extends Activity {

    private static final String COLOR_ACCENT = "#F5A623";
    private static final String COLOR_ACCENT_LIGHT = "#FFD066";
    private static final String COLOR_BG = "#050507";
    private static final String COLOR_TEXT = "#FFFFFF";
    private static final String COLOR_TEXT_SOFT = "#C5CCD8";

    private static final long SCREEN_OCR_INTERVAL_MS = 500L;
    private static final int PIXEL_BLOCK_SIZE = 14;
    private static final int CAPTURE_W = 1280;
    private static final int CAPTURE_H = 720;

    private static final int REQ_OVERLAY_PERMISSION = 101;
    private static final int REQ_MEDIA_PROJECTION = 102;

    private static MediaProjection sMediaProjection;
    private static VirtualDisplay sVirtualDisplay;
    private static ImageReader sImageReader;
    private static Bitmap sLatestCleanGameBitmap;

    private String roomCode;
    private boolean isArabic = true;
    private boolean isPhonePaired = false;

    private String currentTvSubMode = "camera";
    private boolean isScreenTranslationRunning = false;

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

    private WindowManager windowManager;
    private FrameLayout fullScreenOverlayStage;
    private FrameLayout screenItemsOverlayLayer;
    private FrameLayout subtitleBannerBox;
    private TextView subtitleTextView;
    private GradientDrawable boxBackground;
    private WindowManager.LayoutParams stageWindowParams;
    private PowerManager.WakeLock wakeLock;

    private MediaProjectionManager projectionManager;
    private TextRecognizer mlkitRecognizer;
    private boolean isCapturingFrame = false;

    private int realScreenW = 1920;
    private int realScreenH = 1080;

    private JSONObject lastStyleJson = null;

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
            uiHandler.postDelayed(this, 1500);
        }
    };

    private final Runnable screenOcrLoopRunnable = new Runnable() {
        @Override
        public void run() {
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

    public static class SiyaqScreenCaptureService extends Service {
        @Override
        public int onStartCommand(Intent intent, int flags, int startId) {
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
        public IBinder onBind(Intent intent) {
            return null;
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
                requestScreenBroadcastOnly();
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
            btnBroadcast.setText(broadcastReady ? "وضع البث: مفعّل ✓" : "تفعيل وضع البث");
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
            btnBroadcast.setText(broadcastReady ? "Screen Broadcast: Active ✓" : "Enable Screen Broadcast");
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
            Toast.makeText(this, isArabic ? "وضع البث مفعّل وجاهز ✓" : "Screen Broadcast Active ✓", Toast.LENGTH_SHORT).show();
            return;
        }

        try {
            Intent svcIntent = new Intent(this, SiyaqScreenCaptureService.class);
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                startForegroundService(svcIntent);
            } else {
                startService(svcIntent);
            }
        } catch (Exception ignored) {}

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
                }, 350);
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
                }
            }, uiHandler);

            int dpi = getResources().getDisplayMetrics().densityDpi;
            sImageReader = ImageReader.newInstance(CAPTURE_W, CAPTURE_H, PixelFormat.RGBA_8888, 2);
            sVirtualDisplay = sMediaProjection.createVirtualDisplay(
                    "SiyaqTvCapture",
                    CAPTURE_W,
                    CAPTURE_H,
                    dpi,
                    DisplayManager.VIRTUAL_DISPLAY_FLAG_AUTO_MIRROR,
                    sImageReader.getSurface(),
                    null,
                    uiHandler
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
            if (screenItemsOverlayLayer != null) screenItemsOverlayLayer.removeAllViews();
            subtitleTextView.setText(isArabic
                    ? "اختبار شريط الترجمة — جاهز للعرض فوق اللعبة"
                    : "Subtitle Bar Test — Ready over game");
            subtitleBannerBox.setVisibility(View.VISIBLE);
            positionBannerAccurately(0.50f, 0.82f);

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
                "    keepalive: 15," +
                "    reconnectPeriod: 800," +
                "    clean: true" +
                "  });" +
                "  window.mqttClient.on('connect', () => { window.mqttClient.subscribe('siyaq/tv/sec/" + roomCode + "'); });" +
                "  window.mqttClient.on('message', (t, p) => { SiyaqTvWaitBridge.onSyncEvent(p.toString()); });" +
                "} catch(e) {}" +
                "</script></body></html>";
        qrAndMqttWebView.loadDataWithBaseURL("https://siyaq.app", html, "text/html", "UTF-8", null);
    }

    private void handleIncomingPhoneMessage(String jsonStr) {
        try {
            JSONObject obj = new JSONObject(jsonStr);
            if ("tv".equals(obj.optString("sender", ""))) return;

            String type = obj.optString("type", "");

            if ("UNPAIRED".equals(type)) {
                isScreenTranslationRunning = false;
                hideOverlayStage();
                isPhonePaired = false;
                updateUiForPairingState(false);
                rotateToFreshRoomCode();
                Toast.makeText(this, isArabic ? "تم إلغاء الاقتران" : "Unpaired", Toast.LENGTH_SHORT).show();
                return;
            }

            if ("SUB_CLEAR".equals(type)) {
                if (subtitleBannerBox != null) {
                    subtitleTextView.setText("");
                    subtitleBannerBox.setVisibility(View.GONE);
                }
                if (screenItemsOverlayLayer != null) {
                    screenItemsOverlayLayer.removeAllViews();
                }
                return;
            }

            if ("STYLE_UPDATE".equals(type)) {
                JSONObject style = obj.optJSONObject("style");
                if (style != null) {
                    lastStyleJson = style;
                    if ("camera".equals(currentTvSubMode)) {
                        applySmoothHardwareSubtitleStyle(style);
                    }
                }
                return;
            }

            if ("TV_MODE_SWITCH".equals(type)) {
                String mode = obj.optString("mode", "");
                String subMode = obj.optString("tvSubMode", "");
                boolean active = obj.optBoolean("active", false);
                JSONObject style = obj.optJSONObject("style");
                if (style != null) lastStyleJson = style;

                if ("screen_ocr".equals(mode) || "screen".equals(subMode)) {
                    currentTvSubMode = "screen";
                    isScreenTranslationRunning = active;

                    if (subtitleBannerBox != null) {
                        subtitleTextView.setText("");
                        subtitleBannerBox.setVisibility(View.GONE);
                    }
                    if (!active && screenItemsOverlayLayer != null) {
                        screenItemsOverlayLayer.removeAllViews();
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
                    if (screenItemsOverlayLayer != null) {
                        screenItemsOverlayLayer.removeAllViews();
                    }
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

                JSONObject style = obj.optJSONObject("style");
                if (style != null) lastStyleJson = style;

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
                    if (screenItemsOverlayLayer != null) screenItemsOverlayLayer.removeAllViews();
                    subtitleTextView.setText(isArabic ? "متصل بالجوال (وضع الكاميرا) — جاهز للترجمة" : "Connected (Camera Mode) — Ready");
                    subtitleBannerBox.setVisibility(View.VISIBLE);
                    if (lastStyleJson != null) {
                        applySmoothHardwareSubtitleStyle(lastStyleJson);
                    } else {
                        positionBannerAccurately(0.50f, 0.82f);
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
                ensureOverlayStageCreated();
                JSONObject style = obj.optJSONObject("style");
                if (style != null) lastStyleJson = style;
                renderScreenOverlayItems(obj.optJSONArray("items"));
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
                if (screenItemsOverlayLayer != null) {
                    screenItemsOverlayLayer.removeAllViews();
                }

                JSONObject style = obj.optJSONObject("style");
                if (style != null) lastStyleJson = style;

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
                        positionBannerAccurately(0.50f, 0.82f);
                    }
                }
            }
        } catch (Exception ignored) {}
    }

    private void captureCleanGameScreenAndReadText() {
        if (sImageReader == null || mlkitRecognizer == null) return;
        isCapturingFrame = true;

        if (fullScreenOverlayStage != null) {
            fullScreenOverlayStage.setAlpha(0f);
        }

        uiHandler.postDelayed(new Runnable() {
            @Override
            public void run() {
                Image img = null;
                try {
                    img = sImageReader.acquireLatestImage();
                    if (fullScreenOverlayStage != null) {
                        fullScreenOverlayStage.setAlpha(1f);
                    }

                    if (img != null) {
                        Image.Plane[] planes = img.getPlanes();
                        ByteBuffer buffer = planes[0].getBuffer();
                        int pixelStride = planes[0].getPixelStride();
                        int rowStride = planes[0].getRowStride();
                        int rowPadding = rowStride - pixelStride * CAPTURE_W;

                        Bitmap paddedBitmap = Bitmap.createBitmap(
                                CAPTURE_W + rowPadding / pixelStride,
                                CAPTURE_H,
                                Bitmap.Config.ARGB_8888
                        );
                        paddedBitmap.copyPixelsFromBuffer(buffer);
                        img.close();
                        img = null;

                        Bitmap cleanBitmap = Bitmap.createBitmap(paddedBitmap, 0, 0, CAPTURE_W, CAPTURE_H);
                        paddedBitmap.recycle();

                        if (sLatestCleanGameBitmap != null && !sLatestCleanGameBitmap.isRecycled()) {
                            sLatestCleanGameBitmap.recycle();
                        }
                        sLatestCleanGameBitmap = cleanBitmap;
                    }

                    if (sLatestCleanGameBitmap == null || sLatestCleanGameBitmap.isRecycled()) {
                        isCapturingFrame = false;
                        return;
                    }

                    InputImage inputImage = InputImage.fromBitmap(sLatestCleanGameBitmap, 0);
                    mlkitRecognizer.process(inputImage)
                            .addOnSuccessListener(visionText -> {
                                publishDetectedScreenBlocksToPhone(visionText);
                                isCapturingFrame = false;
                            })
                            .addOnFailureListener(e -> isCapturingFrame = false);

                } catch (Exception e) {
                    if (img != null) {
                        try { img.close(); } catch (Exception ignored) {}
                    }
                    if (fullScreenOverlayStage != null) {
                        fullScreenOverlayStage.setAlpha(1f);
                    }
                    isCapturingFrame = false;
                }
            }
        }, 35);
    }

    private void publishDetectedScreenBlocksToPhone(Text visionText) {
        if (!isPhonePaired || !"screen".equals(currentTvSubMode) || qrAndMqttWebView == null) return;
        try {
            JSONArray blocksArray = new JSONArray();
            int idx = 0;

            for (Text.TextBlock block : visionText.getTextBlocks()) {
                String text = block.getText() != null ? block.getText().trim() : "";
                Rect box = block.getBoundingBox();
                if (text.isEmpty() || box == null) continue;

                if (text.matches(".*[\u0600-\u06FF].*")) continue;

                double normX = Math.max(0.0, Math.min(0.98, (double) box.left / CAPTURE_W));
                double normY = Math.max(0.0, Math.min(0.98, (double) box.top / CAPTURE_H));
                double normW = Math.max(0.04, Math.min(1.0 - normX, (double) box.width() / CAPTURE_W));
                double normH = Math.max(0.025, Math.min(1.0 - normY, (double) box.height() / CAPTURE_H));

                JSONObject bObj = new JSONObject();
                bObj.put("id", "pos_" + Math.round(normX * 25) + "_" + Math.round(normY * 25) + "_" + idx);
                bObj.put("text", text);
                bObj.put("x", normX);
                bObj.put("y", normY);
                bObj.put("w", normW);
                bObj.put("h", normH);
                blocksArray.put(bObj);
                idx++;
            }

            JSONObject payload = new JSONObject();
            payload.put("type", "SCREEN_TEXTS_BATCH");
            payload.put("sender", "tv");
            payload.put("frameId", System.currentTimeMillis());
            payload.put("screenWidth", CAPTURE_W);
            payload.put("screenHeight", CAPTURE_H);
            payload.put("blocks", blocksArray);

            String escapedJson = JSONObject.quote(payload.toString());
            qrAndMqttWebView.evaluateJavascript(
                    "if(window.mqttClient && window.mqttClient.connected){ window.mqttClient.publish('siyaq/tv/sec/" + roomCode + "', " + escapedJson + "); }",
                    null
            );
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
            int stepX = Math.max(2, safeW / 16);
            int stepY = Math.max(2, safeH / 6);

            int topSampleY = Math.max(0, safeY - 3);
            int botSampleY = Math.min(bmpH - 1, safeY + safeH + 2);
            for (int sx = safeX; sx < safeX + safeW; sx += stepX) {
                int pTop = gameBitmap.getPixel(sx, topSampleY);
                int pBot = gameBitmap.getPixel(sx, botSampleY);
                borderR += Color.red(pTop) + Color.red(pBot);
                borderG += Color.green(pTop) + Color.green(pBot);
                borderB += Color.blue(pTop) + Color.blue(pBot);
                borderCount += 2;
            }
            for (int sy = safeY; sy < safeY + safeH; sy += stepY) {
                int leftSampleX = Math.max(0, safeX - 3);
                int rightSampleX = Math.min(bmpW - 1, safeX + safeW + 2);
                int pLeft = gameBitmap.getPixel(leftSampleX, sy);
                int pRight = gameBitmap.getPixel(rightSampleX, sy);
                borderR += Color.red(pLeft) + Color.red(pRight);
                borderG += Color.green(pLeft) + Color.green(pRight);
                borderB += Color.blue(pLeft) + Color.blue(pRight);
                borderCount += 2;
            }

            int baseR = borderCount > 0 ? borderR / borderCount : 24;
            int baseG = borderCount > 0 ? borderG / borderCount : 28;
            int baseB = borderCount > 0 ? borderB / borderCount : 38;
            int baseLum = (baseR * 77 + baseG * 150 + baseB * 29) >> 8;

            Bitmap mosaicBitmap = Bitmap.createBitmap(safeW, safeH, Bitmap.Config.ARGB_8888);
            Canvas canvas = new Canvas(mosaicBitmap);
            Paint blockPaint = new Paint();
            blockPaint.setStyle(Paint.Style.FILL);
            blockPaint.setAntiAlias(false);

            int blockSize = Math.max(8, PIXEL_BLOCK_SIZE);

            for (int by = 0; by < safeH; by += blockSize) {
                for (int bx = 0; bx < safeW; bx += blockSize) {
                    int rSum = 0, gSum = 0, bSum = 0, count = 0;

                    for (int dy = 0; dy < blockSize && (by + dy) < safeH; dy += 2) {
                        for (int dx = 0; dx < blockSize && (bx + dx) < safeW; dx += 2) {
                            int px = gameBitmap.getPixel(safeX + bx + dx, safeY + by + dy);
                            int r = Color.red(px);
                            int g = Color.green(px);
                            int b = Color.blue(px);
                            int lum = (r * 77 + g * 150 + b * 29) >> 8;

                            if (Math.abs(lum - baseLum) < 52 && lum < 180) {
                                rSum += r;
                                gSum += g;
                                bSum += b;
                                count++;
                            }
                        }
                    }

                    int cellR = count > 0 ? (rSum / count) : baseR;
                    int cellG = count > 0 ? (gSum / count) : baseG;
                    int cellB = count > 0 ? (bSum / count) : baseB;

                    cellR = (int) (((cellR * 70 + baseR * 30) / 100) * 0.88f);
                    cellG = (int) (((cellG * 70 + baseG * 30) / 100) * 0.88f);
                    cellB = (int) (((cellB * 70 + baseB * 30) / 100) * 0.88f);

                    blockPaint.setColor(Color.argb(255, cellR, cellG, cellB));
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

        screenItemsOverlayLayer = new FrameLayout(this);
        screenItemsOverlayLayer.setLayoutDirection(View.LAYOUT_DIRECTION_LTR);
        screenItemsOverlayLayer.setBackgroundColor(Color.TRANSPARENT);
        fullScreenOverlayStage.addView(screenItemsOverlayLayer, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT,
                FrameLayout.LayoutParams.MATCH_PARENT
        ));

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

    private void renderScreenOverlayItems(JSONArray items) {
        if (screenItemsOverlayLayer == null) return;
        if (subtitleBannerBox != null) subtitleBannerBox.setVisibility(View.GONE);

        screenItemsOverlayLayer.removeAllViews();
        if (items == null || items.length() == 0) return;

        boolean useCamouflage = lastStyleJson != null && lastStyleJson.optBoolean("camouflageBlurMode", false);
        String fontFamilyRaw = lastStyleJson != null ? lastStyleJson.optString("fontFamily", "Tajawal") : "Tajawal";
        boolean isBold = lastStyleJson == null || lastStyleJson.optBoolean("isBold", true);
        String textColorStr = lastStyleJson != null ? lastStyleJson.optString("textColor", "#FFFFFF") : "#FFFFFF";
        int textOpacity = lastStyleJson != null ? lastStyleJson.optInt("textOpacity", 100) : 100;
        String bgColorStr = lastStyleJson != null ? lastStyleJson.optString("bgColor", "#000000") : "#000000";
        int bgOpacity = lastStyleJson != null ? lastStyleJson.optInt("bgOpacity", 95) : 95;

        int parsedTextCol;
        try { parsedTextCol = Color.parseColor(textColorStr); } catch (Exception e) { parsedTextCol = Color.WHITE; }
        int textAlpha = textOpacity >= 99 ? 255 : Math.max(40, Math.min(255, Math.round(textOpacity * 2.55f)));
        int finalTextColor = Color.argb(textAlpha, Color.red(parsedTextCol), Color.green(parsedTextCol), Color.blue(parsedTextCol));
        Typeface tf = resolveRequestedArabicTypeface(fontFamilyRaw, isBold);

        for (int i = 0; i < items.length(); i++) {
            JSONObject item = items.optJSONObject(i);
            if (item == null) continue;

            String arText = item.optString("ar", "").trim();
            if (arText.isEmpty()) continue;

            double nx = item.optDouble("x", 0.1);
            double ny = item.optDouble("y", 0.5);
            double nw = item.optDouble("w", 0.2);
            double nh = item.optDouble("h", 0.05);

            int padCoverX = 12;
            int padCoverY = 6;
            int pxX = Math.max(0, (int) Math.round(nx * realScreenW) - padCoverX);
            int pxY = Math.max(0, (int) Math.round(ny * realScreenH) - padCoverY);
            int pxW = Math.max(72, (int) Math.round(nw * realScreenW) + (padCoverX * 2));
            int pxH = Math.max(34, (int) Math.round(nh * realScreenH) + (padCoverY * 2));

            TextView tv = new TextView(this);
            tv.setText(arText);
            tv.setTextColor(finalTextColor);
            tv.setTypeface(tf);
            tv.getPaint().setFakeBoldText(isBold);
            tv.setGravity(Gravity.CENTER);
            tv.setTextDirection(View.TEXT_DIRECTION_RTL);
            tv.setIncludeFontPadding(false);
            tv.setPadding(10, 4, 10, 4);
            tv.setShadowLayer(4f, 0f, 2f, Color.argb(245, 0, 0, 0));

            int charLen = Math.max(1, arText.length());
            float heightBasedPx = pxH * 0.54f;
            float areaBasedPx = (float) Math.sqrt((pxW * pxH) / (double) Math.max(4, charLen * 1.30));
            float autoMatchedPx = Math.max(18f, Math.min(54f, Math.min(heightBasedPx, areaBasedPx * 1.25f)));
            tv.setTextSize(TypedValue.COMPLEX_UNIT_PX, autoMatchedPx);

            if (useCamouflage && sLatestCleanGameBitmap != null) {
                BitmapDrawable pixelPatch = buildTruePixelatedCamouflage(sLatestCleanGameBitmap, nx, ny, nw, nh);
                if (pixelPatch != null) {
                    tv.setBackground(pixelPatch);
                } else {
                    tv.setBackgroundColor(Color.argb(255, 20, 24, 34));
                }
            } else {
                int parsedBg;
                try { parsedBg = Color.parseColor(bgColorStr); } catch (Exception e) { parsedBg = Color.BLACK; }
                int solidAlpha = Math.max(230, Math.min(255, Math.round(bgOpacity * 2.55f)));
                GradientDrawable customBg = new GradientDrawable();
                customBg.setColor(Color.argb(solidAlpha, Color.red(parsedBg), Color.green(parsedBg), Color.blue(parsedBg)));
                customBg.setCornerRadius(4f);
                tv.setBackground(customBg);
            }

            FrameLayout.LayoutParams lp = new FrameLayout.LayoutParams(pxW, pxH, Gravity.TOP | Gravity.LEFT);
            lp.leftMargin = Math.max(0, Math.min(realScreenW - pxW, pxX));
            lp.topMargin = Math.max(0, Math.min(realScreenH - pxH, pxY));
            screenItemsOverlayLayer.addView(tv, lp);
        }
    }

    private void positionBannerAccurately(float normCenterX, float normCenterY) {
        if (subtitleBannerBox == null) return;

        int specW = View.MeasureSpec.makeMeasureSpec(realScreenW, View.MeasureSpec.AT_MOST);
        int specH = View.MeasureSpec.makeMeasureSpec(realScreenH, View.MeasureSpec.AT_MOST);
        subtitleBannerBox.measure(specW, specH);

        int boxW = subtitleBannerBox.getMeasuredWidth();
        int boxH = subtitleBannerBox.getMeasuredHeight();

        float centerX = realScreenW * normCenterX;
        float centerY = realScreenH * normCenterY;

        float targetX = Math.max(0f, Math.min(realScreenW - boxW, centerX - (boxW / 2f)));
        float targetY = Math.max(0f, Math.min(realScreenH - boxH, centerY - (boxH / 2f)));

        subtitleBannerBox.setTranslationX(targetX);
        subtitleBannerBox.setTranslationY(targetY);
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
            positionBannerAccurately(posX / 100f, posY / 100f);
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
        isScreenTranslationRunning = false;
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
        Toast.makeText(this, isArabic ? "تم إلغاء الاقتران" : "Unpaired", Toast.LENGTH_SHORT).show();
    }

    private void hideOverlayStage() {
        if (fullScreenOverlayStage != null && windowManager != null) {
            try {
                windowManager.removeView(fullScreenOverlayStage);
            } catch (Exception ignored) {}
            fullScreenOverlayStage = null;
            screenItemsOverlayLayer = null;
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
        uiHandler.removeCallbacks(keepAliveRunnable);
        uiHandler.removeCallbacks(screenOcrLoopRunnable);
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