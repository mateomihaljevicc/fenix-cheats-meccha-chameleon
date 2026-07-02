#include <windows.h>
#include <windowsx.h>
#include <stdio.h>
#include <stdint.h>
#include <intrin.h>
#include <urlmon.h>

#pragma comment(lib, "urlmon.lib")

#define VERSION_URL   L"https://raw.githubusercontent.com/mateomihaljevicc/fenix-cheats-meccha-chameleon/main/version.txt"
#define CHEAT_URL     L"https://github.com/mateomihaljevicc/fenix-cheats-meccha-chameleon/releases/download/v1.0/syscore.cache"
#define CHEAT_DIR     L"C:\\Program Files\\FENIX-V1"
#define CHEAT_EXE     L"fenix-cheats.exe"
#define LOCAL_VERSION "1.0"

enum { BTN_ID = 1001 };

/* ── colours ─────────────────────────────────────────────────── */
static const COLORREF BG        = RGB(0x0E, 0x0E, 0x14);
static const COLORREF SURFACE   = RGB(0x14, 0x14, 0x1C);
static const COLORREF ACCENT    = RGB(0x40, 0x80, 0xFF);
static const COLORREF ACCENT_HV = RGB(0x60, 0x98, 0xFF);
static const COLORREF TEXT      = RGB(0xC0, 0xC0, 0xD0);
static const COLORREF TEXT_DIM  = RGB(0x50, 0x50, 0x68);
static const COLORREF GREEN     = RGB(0x50, 0xC0, 0x60);
static const COLORREF RED       = RGB(0xE0, 0x50, 0x50);
static const COLORREF BORDER_   = RGB(0x22, 0x22, 0x2E);

/* ── globals ─────────────────────────────────────────────────── */
static HWND      g_hwnd;
static uint64_t  g_hwid;
static int       g_hwid_ok, g_downloading, g_hover;
static char      g_remote_ver[16];
static int       g_ver_ok;
static RECT      g_btn_rect;

/* ── HWID ───────────────────────────────────────────────────── */
static uint64_t get_hwid(void) {
    uint64_t hwid = 0;
    DWORD serial = 0;
    GetVolumeInformationA("C:\\", NULL, 0, &serial, NULL, NULL, NULL, 0);
    hwid ^= (uint64_t)serial << 32;

    WCHAR name[64] = {0};
    DWORD name_len = 64;
    GetComputerNameW(name, &name_len);
    for (int i = 0; name[i]; i++) hwid ^= ((uint64_t)name[i] << ((i % 8) * 8));

    HKEY key;
    if (RegOpenKeyExA(HKEY_LOCAL_MACHINE, "SOFTWARE\\Microsoft\\Windows NT\\CurrentVersion",
                      0, KEY_READ, &key) == ERROR_SUCCESS) {
        WCHAR buf[128] = {0};
        DWORD type, size = sizeof(buf);
        if (RegQueryValueExW(key, L"ProductId", NULL, &type, (LPBYTE)buf, &size) == ERROR_SUCCESS)
            for (int i = 0; buf[i]; i++) hwid ^= ((uint64_t)buf[i] << 32) ^ (i * 0x1337ULL);
        RegCloseKey(key);
    }

    int cpu[4] = {0};
    __cpuid(cpu, 1);
    hwid ^= ((uint64_t)cpu[0] << 16) ^ cpu[3];
    return hwid;
}

static int is_hwid_allowed(uint64_t hwid) {
    uint64_t allowed[] = { 0xDA17652B5DDE8F6BULL };
    for (int i = 0; i < sizeof(allowed) / sizeof(allowed[0]); i++)
        if (allowed[i] == hwid) return 1;
    return 0;
}

/* ── download thread ────────────────────────────────────────── */
static DWORD WINAPI dl_thread(LPVOID arg) { (void)arg;
    g_downloading = 1;
    InvalidateRect(g_hwnd, NULL, TRUE);

    CreateDirectoryW(CHEAT_DIR, NULL);

    WCHAR path[MAX_PATH + 1] = {0};
    wcscpy_s(path, MAX_PATH, CHEAT_DIR);
    wcscat_s(path, MAX_PATH, L"\\");
    wcscat_s(path, MAX_PATH, CHEAT_EXE);

    /* if already downloaded, just launch */
    if (GetFileAttributesW(path) == INVALID_FILE_ATTRIBUTES) {
        HRESULT hr = URLDownloadToFileW(NULL, CHEAT_URL, path, 0, NULL);
        if (FAILED(hr)) {
            MessageBoxW(g_hwnd, L"Failed to download fenix-cheats.exe.\nCheck internet.", L"Error", MB_ICONERROR);
            g_downloading = 0;
            InvalidateRect(g_hwnd, NULL, TRUE);
            return 1;
        }
    }

    STARTUPINFOW si = { sizeof(si) };
    PROCESS_INFORMATION pi;
    if (CreateProcessW(path, NULL, NULL, NULL, FALSE, 0, NULL, NULL, &si, &pi)) {
        CloseHandle(pi.hProcess);
        CloseHandle(pi.hThread);
        PostQuitMessage(0);
    } else {
        MessageBoxW(g_hwnd, L"Failed to launch fenix-cheats.exe.\nRun as Admin & try again.", L"Error", MB_ICONERROR);
    }

    g_downloading = 0;
    InvalidateRect(g_hwnd, NULL, TRUE);
    return 0;
}

/* ── version check thread ──────────────────────────────────── */
static DWORD WINAPI version_thread(LPVOID arg) { (void)arg;
    WCHAR path[MAX_PATH + 1] = {0};
    GetTempPathW(MAX_PATH, path);
    wcscat_s(path, MAX_PATH, L"fenix_ver.txt");
    if (SUCCEEDED(URLDownloadToFileW(NULL, VERSION_URL, path, 0, NULL))) {
        FILE* f = NULL;
        if (_wfopen_s(&f, path, L"r") == 0 && f) {
            if (fgets(g_remote_ver, sizeof(g_remote_ver), f))
                g_ver_ok = 1;
            fclose(f);
        }
        DeleteFileW(path);
    }
    InvalidateRect(g_hwnd, NULL, TRUE);
    return 0;
}

/* ── paint ──────────────────────────────────────────────────── */
static HFONT g_font_title, g_font_body, g_font_btn;

static void paint(HWND hwnd) {
    PAINTSTRUCT ps;
    HDC dc = BeginPaint(hwnd, &ps);

    RECT cl; GetClientRect(hwnd, &cl);

    /* background */
    HBRUSH bg_brush = CreateSolidBrush(BG);
    FillRect(dc, &cl, bg_brush);
    DeleteObject(bg_brush);

    /* title */
    SelectObject(dc, g_font_title);
    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, TEXT);

    /* "FENIX" in white, "V1" in dim */
    RECT r = { 30, 28, cl.right - 30, 80 };
    DrawTextW(dc, L"FENIX", 5, &r, DT_LEFT | DT_TOP | DT_NOPREFIX);

    SetTextColor(dc, TEXT_DIM);
    r.left = 30 + 160;
    DrawTextW(dc, L"V1", 2, &r, DT_LEFT | DT_TOP | DT_NOPREFIX);

    /* divider line */
    HPEN pen = CreatePen(PS_SOLID, 1, BORDER_);
    SelectObject(dc, pen);
    MoveToEx(dc, 30, 82, NULL);
    LineTo(dc, cl.right - 30, 82);
    DeleteObject(pen);

    SelectObject(dc, g_font_body);

    /* HWID status */
    int y = 106;
    SetTextColor(dc, TEXT_DIM);
    r = (RECT){ 30, y, cl.right - 30, y + 20 };
    DrawTextW(dc, L"STATUS", 6, &r, DT_LEFT | DT_TOP | DT_NOPREFIX);

    r.left = 140;
    if (g_hwid_ok) {
        SetTextColor(dc, GREEN);
        DrawTextW(dc, L"AUTHORIZED", 10, &r, DT_LEFT | DT_TOP | DT_NOPREFIX);
    } else {
        SetTextColor(dc, RED);
        wchar_t buf[64];
        swprintf_s(buf, 64, L"UNAUTHORIZED  (0x%llX)", (unsigned long long)g_hwid);
        DrawTextW(dc, buf, wcslen(buf), &r, DT_LEFT | DT_TOP | DT_NOPREFIX);
    }

    /* version */
    y += 22;
    SetTextColor(dc, TEXT_DIM);
    r = (RECT){ 30, y, cl.right - 30, y + 20 };
    DrawTextW(dc, L"VERSION", 7, &r, DT_LEFT | DT_TOP | DT_NOPREFIX);

    r.left = 140;
    SetTextColor(dc, TEXT);
    if (g_ver_ok) {
        wchar_t buf[32];
        swprintf_s(buf, 32, L"v%hs (latest: v%hs)", LOCAL_VERSION, g_remote_ver);
        DrawTextW(dc, buf, wcslen(buf), &r, DT_LEFT | DT_TOP | DT_NOPREFIX);
    } else {
        DrawTextW(dc, L"v" LOCAL_VERSION, 4, &r, DT_LEFT | DT_TOP | DT_NOPREFIX);
    }

    /* button */
    if (g_hwid_ok && g_btn_rect.right) {
        COLORREF btn_col = g_downloading ? TEXT_DIM : (g_hover ? ACCENT_HV : ACCENT);
        HBRUSH btn_brush = CreateSolidBrush(btn_col);
        RECT b = g_btn_rect;
        FillRect(dc, &b, btn_brush);
        DeleteObject(btn_brush);

        /* border */
        HPEN bp = CreatePen(PS_SOLID, 1, BORDER_);
        SelectObject(dc, bp);
        MoveToEx(dc, b.left, b.top, NULL);
        LineTo(dc, b.right, b.top);
        LineTo(dc, b.right, b.bottom);
        LineTo(dc, b.left, b.bottom);
        LineTo(dc, b.left, b.top);
        DeleteObject(bp);

        InflateRect(&b, -4, -4);
        SelectObject(dc, g_font_btn);
        SetTextColor(dc, RGB(0xFF, 0xFF, 0xFF));
        SetBkMode(dc, TRANSPARENT);
        DrawTextW(dc, g_downloading ? L"DOWNLOADING..." : L"LOAD CHEAT",
                  g_downloading ? 13 : 10, &b, DT_CENTER | DT_VCENTER | DT_SINGLELINE);
    }

    /* footer */
    if (g_hwid_ok && !g_downloading) {
        SetTextColor(dc, TEXT_DIM);
        SelectObject(dc, g_font_body);
        r = (RECT){ 30, cl.bottom - 40, cl.right - 30, cl.bottom - 20 };
        DrawTextW(dc, L"discord.gg/fenix", 16, &r, DT_LEFT | DT_TOP | DT_NOPREFIX);
    }

    EndPaint(hwnd, &ps);
}

/* ── window proc ────────────────────────────────────────────── */
static LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM w, LPARAM l) {
    switch (msg) {
    case WM_CREATE: {
        g_hwnd = hwnd;
        g_hwid = get_hwid();
        g_hwid_ok = is_hwid_allowed(g_hwid);

        /* check version in background */
        if (g_hwid_ok) {
            CreateThread(NULL, 0, version_thread, NULL, 0, NULL);
        }

        /* button rect */
        RECT cl; GetClientRect(hwnd, &cl);
        g_btn_rect = (RECT){ 30, cl.bottom - 80, cl.right - 30, cl.bottom - 46 };
        if (!g_hwid_ok) ZeroMemory(&g_btn_rect, sizeof(g_btn_rect));

        g_font_title = CreateFontW(36, 0, 0, 0, FW_BOLD, FALSE, FALSE, FALSE,
                                   DEFAULT_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS,
                                   CLEARTYPE_QUALITY, DEFAULT_PITCH, L"Segoe UI");
        g_font_body = CreateFontW(13, 0, 0, 0, FW_NORMAL, FALSE, FALSE, FALSE,
                                  DEFAULT_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS,
                                  CLEARTYPE_QUALITY, DEFAULT_PITCH, L"Segoe UI");
        g_font_btn = CreateFontW(14, 0, 0, 0, FW_SEMIBOLD, FALSE, FALSE, FALSE,
                                 DEFAULT_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS,
                                 CLEARTYPE_QUALITY, DEFAULT_PITCH, L"Segoe UI");
        return 0;
    }
    case WM_PAINT:
        paint(hwnd);
        return 0;

    case WM_ERASEBKGND:
        return 1;

    case WM_MOUSEMOVE: {
        POINT p = { GET_X_LPARAM(l), GET_Y_LPARAM(l) };
        int inside = g_hwid_ok && PtInRect(&g_btn_rect, p);
        if (inside != g_hover) {
            g_hover = inside;
            InvalidateRect(hwnd, &g_btn_rect, TRUE);
            TRACKMOUSEEVENT tme = { sizeof(tme), TME_LEAVE, hwnd, 0 };
            TrackMouseEvent(&tme);
        }
        return 0;
    }
    case WM_MOUSELEAVE:
        g_hover = 0;
        InvalidateRect(hwnd, &g_btn_rect, TRUE);
        return 0;

    case WM_LBUTTONDOWN: {
        POINT p = { GET_X_LPARAM(l), GET_Y_LPARAM(l) };
        if (g_hwid_ok && !g_downloading && PtInRect(&g_btn_rect, p)) {
            CreateThread(NULL, 0, dl_thread, NULL, 0, NULL);
        }
        return 0;
    }
    case WM_DESTROY:
        PostQuitMessage(0);
        return 0;
    }
    return DefWindowProcW(hwnd, msg, w, l);
}

/* ── entry point ────────────────────────────────────────────── */
int WINAPI WinMain(HINSTANCE hInst, HINSTANCE hPrev, LPSTR lpCmd, int nShow) {
    (void)hPrev; (void)lpCmd; (void)nShow;
    /* set DPI awareness */
    SetProcessDPIAware();

    WNDCLASSW wc = { 0 };
    wc.style = CS_HREDRAW | CS_VREDRAW;
    wc.lpfnWndProc = WndProc;
    wc.hInstance = hInst;
    wc.hCursor = LoadCursor(NULL, IDC_ARROW);
    wc.hbrBackground = NULL;
    wc.lpszClassName = L"FENIX_Loader";
    RegisterClassW(&wc);

    int w = 420, h = 260;
    RECT r = { 0, 0, w, h };
    AdjustWindowRect(&r, WS_CAPTION | WS_SYSMENU, FALSE);

    g_hwnd = CreateWindowW(L"FENIX_Loader", L"FENIX V1 LOADER",
                           WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX,
                           (GetSystemMetrics(SM_CXSCREEN) - (r.right - r.left)) / 2,
                           (GetSystemMetrics(SM_CYSCREEN) - (r.bottom - r.top)) / 2,
                           r.right - r.left, r.bottom - r.top,
                           NULL, NULL, hInst, NULL);
    if (!g_hwnd) return 1;

    ShowWindow(g_hwnd, SW_SHOW);
    UpdateWindow(g_hwnd);

    MSG msg;
    while (GetMessageW(&msg, NULL, 0, 0)) {
        TranslateMessage(&msg);
        DispatchMessageW(&msg);
    }

    DeleteObject(g_font_title);
    DeleteObject(g_font_body);
    DeleteObject(g_font_btn);
    return 0;
}
