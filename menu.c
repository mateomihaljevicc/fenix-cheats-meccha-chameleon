/*
 * MECCHA CHAMELEON (PenguinHotel) - External ESP
 * UE 5.6.1-44394996 -- offsets from Dumper-7 SDK dump
 *
 * Usermode ReadProcessMemory, GDI overlay.
 * Build: build.bat
 */
 
#pragma comment(linker, "/SUBSYSTEM:WINDOWS /ENTRY:mainCRTStartup")
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <windowsx.h>
#include <dwmapi.h>
#include <math.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <tlhelp32.h>
 
#pragma comment(lib, "user32.lib")
#pragma comment(lib, "gdi32.lib")
#pragma comment(lib, "dwmapi.lib")
 
/* ── usermode RPM ──────────────────────────────────────────── */
 
static HANDLE   g_proc = NULL;
static uint32_t g_pid  = 0;
static uint64_t g_base = 0;
 
static int rpm(uint64_t addr, void* buf, uint32_t size) {
    SIZE_T n;
    if (!g_proc || !addr) return 0;
    return ReadProcessMemory(g_proc, (LPCVOID)addr, buf, size, &n) && n == size;
}
 
static uint64_t read64(uint64_t a) { uint64_t v=0; rpm(a,&v,8); return v; }
static uint32_t read32(uint64_t a) { uint32_t v=0; rpm(a,&v,4); return v; }
static float    readf (uint64_t a) { float    v=0; rpm(a,&v,4); return v; }
static double   readd (uint64_t a) { double   v=0; rpm(a,&v,8); return v; }
static uint8_t  read8 (uint64_t a) { uint8_t  v=0; rpm(a,&v,1); return v; }
 
/* ── usermode WPM ──────────────────────────────────────────── */
 
static int wpm(uint64_t addr, void* buf, uint32_t size) {
    SIZE_T n;
    if (!g_proc || !addr) return 0;
    return WriteProcessMemory(g_proc, (LPVOID)addr, buf, size, &n) && n == size;
}
 
static void write64(uint64_t a, uint64_t v) { wpm(a, &v, 8); }
static void writef(uint64_t a, float v)    { wpm(a, &v, 4); }
static void writed(uint64_t a, double v)   { wpm(a, &v, 8); }
 
/* ── sig scanner ───────────────────────────────────────────── */
 
#define SIG_CHUNK 0x10000
 
static uint64_t sig_scan(uint64_t start, uint64_t size,
                         const uint8_t* pattern, const uint8_t* mask, int pat_len) {
    uint8_t buf[SIG_CHUNK];
    for (uint64_t off = 0; off + pat_len <= size; off += SIG_CHUNK - pat_len) {
        uint32_t chunk = (uint32_t)((size - off < SIG_CHUNK) ? size - off : SIG_CHUNK);
        if (!rpm(start + off, buf, chunk)) continue;
        for (uint32_t i = 0; i + pat_len <= chunk; i++) {
            int match = 1;
            for (int j = 0; j < pat_len; j++) {
                if (mask[j] && buf[i+j] != pattern[j]) { match = 0; break; }
            }
            if (match) return start + off + i;
        }
    }
    return 0;
}
 
static uint64_t resolve_rip_relative(uint64_t insn_addr, int insn_len) {
    int32_t rel = 0;
    rpm(insn_addr + insn_len - 4, &rel, 4);
    return insn_addr + insn_len + rel;
}
 
/* ── FName resolution (UE5 FNamePool) ──────────────────────── */
 
static uint64_t g_fname_pool = 0;
#define FNAME_BLOCK_BITS 16
#define FNAME_BLOCK_SIZE (1 << FNAME_BLOCK_BITS)
#define FNAME_BLOCKS_OFF 0x10  /* block pointers start at FNamePool + 0x10 */
 
static int fname_to_string(uint32_t fname_id, char* out, int maxlen) {
    if (!g_fname_pool || !fname_id) { out[0] = 0; return 0; }
    uint32_t block_idx = fname_id >> FNAME_BLOCK_BITS;
    uint32_t entry_off = fname_id & (FNAME_BLOCK_SIZE - 1);
    uint64_t block_ptr = read64(g_fname_pool + FNAME_BLOCKS_OFF + block_idx * 8);
    if (!block_ptr) { out[0] = 0; return 0; }
    uint64_t entry = block_ptr + (uint64_t)entry_off * 2;
    uint16_t header = 0;
    rpm(entry, &header, 2);
    int len = header >> 6;
    if (len <= 0 || len >= maxlen) { out[0] = 0; return 0; }
    rpm(entry + 2, out, len);
    out[len] = 0;
    return len;
}
 
/* ── FProperty walker (UE5 runtime reflection) ─────────────── */
 
/* UE5 FField layout:
   +0x00: vtable
   +0x08: FFieldClass* ClassPrivate
   +0x10: FFieldVariant Owner (8 bytes, tagged ptr)
   +0x18: FField* Next
   +0x20: FName NamePrivate (4 bytes CompIdx + 4 bytes Number)
   +0x28: EObjectFlags FlagsPrivate
*/
#define FFIELD_NEXT   0x18
#define FFIELD_NAME   0x20
 
/* FProperty extends FField:
   +0x30: int32 ArrayDim
   +0x34: int32 ElementSize
   +0x44: int32 Offset_Internal  <-- THE OFFSET WE WANT
*/
#define FPROPERTY_OFFSET 0x44
 
/* UStruct (UClass parent):
   +0x40: UStruct* SuperStruct
   +0x50: FField* ChildProperties (FProperty linked list)
*/
#define USTRUCT_SUPER       0x40
#define USTRUCT_CHILD_PROPS 0x50
 
/* UObject:
   +0x10: UClass* ClassPrivate
*/
#define UOBJECT_CLASS 0x10
 
static int find_property_offset(uint64_t uclass, const char* prop_name, int32_t* out_offset) {
    char name_buf[128];
    uint64_t cls = uclass;
    while (cls) {
        uint64_t prop = read64(cls + USTRUCT_CHILD_PROPS);
        while (prop) {
            uint32_t fname_id = read32(prop + FFIELD_NAME);
            if (fname_id && fname_to_string(fname_id, name_buf, sizeof(name_buf))) {
                if (_stricmp(name_buf, prop_name) == 0) {
                    *out_offset = (int32_t)read32(prop + FPROPERTY_OFFSET);
                    return 1;
                }
            }
            prop = read64(prop + FFIELD_NEXT);
        }
        cls = read64(cls + USTRUCT_SUPER);
    }
    return 0;
}

static void dump_properties(uint64_t uclass, const char* label) {
    char name_buf[128];
    uint64_t cls = uclass;
    printf("[*] %s properties:\n", label);
    while (cls) {
        uint64_t prop = read64(cls + USTRUCT_CHILD_PROPS);
        while (prop) {
            uint32_t fname_id = read32(prop + FFIELD_NAME);
            if (fname_id && fname_to_string(fname_id, name_buf, sizeof(name_buf))) {
                int32_t off = (int32_t)read32(prop + FPROPERTY_OFFSET);
                printf("    +0x%04X %s\n", off, name_buf);
            }
            prop = read64(prop + FFIELD_NEXT);
        }
        cls = read64(cls + USTRUCT_SUPER);
    }
    fflush(stdout);
}
 
/* ── dynamic offset resolution ─────────────────────────────── */
 
static uint64_t g_off_gworld = 0;
 
/* game-specific offsets resolved via reflection */
static int32_t g_off_player_health     = 0x640;  /* fallbacks from SDK */
static int32_t g_off_player_max_health = 0x648;
static int32_t g_off_player_dead       = 0x5AA;
static int32_t g_off_player_mesh       = 0x418;
static int32_t g_off_player_difficulty = 0x624;
static int32_t g_off_player_mesh_xform = 0x900;
static int32_t g_off_enemy_health      = 0x8D8;
static int32_t g_off_enemy_max_health  = 0x908;
static int32_t g_off_enemy_is_down     = 0x8A8;
static int32_t g_off_capsule_height    = 0xB28;
static int32_t g_off_current_weapon    = 0;
static int32_t g_off_ammo_current      = 0;
static int32_t g_off_ammo_max          = 0;

static int resolve_offsets(void) {
    if (!g_base) return 0;
 
    /* get .text section bounds */
    uint16_t e_lfanew = 0;
    rpm(g_base + 0x3C, &e_lfanew, 2);
    uint32_t text_va = 0, text_size = 0;
    rpm(g_base + e_lfanew + 0x2C, &text_va, 4);
    rpm(g_base + e_lfanew + 0x30, &text_size, 4);
    if (!text_va || !text_size) { text_va = 0x1000; text_size = 0x8000000; }
    uint64_t text_start = g_base + text_va;
 
    printf("[*] Scanning .text (0x%X bytes)...\n", text_size);
 
    /* --- GWorld sig --- */
    {
        uint8_t pat[] = {0x48,0x8B,0x1D, 0,0,0,0, 0x48,0x85,0xDB, 0x74,0, 0x41,0xB0,0x01};
        uint8_t msk[] = {1,1,1, 0,0,0,0, 1,1,1, 1,0, 1,1,1};
        uint64_t hit = sig_scan(text_start, text_size, pat, msk, sizeof(pat));
        if (hit) {
            g_off_gworld = resolve_rip_relative(hit, 7) - g_base;
            printf("[+] GWorld: base+0x%llX\n", (unsigned long long)g_off_gworld);
        } else {
            printf("[-] GWorld sig failed, fallback 0xA0B4FF0\n");
            g_off_gworld = 0xA0B4FF0;
        }
    }
 
    /* --- GNames sig: 4C 8D 05 ?? ?? ?? ?? EB ?? 48 8D 0D ?? ?? ?? ?? E8 --- */
    {
        uint8_t pat[] = {0x4C,0x8D,0x05, 0,0,0,0, 0xEB,0, 0x48,0x8D,0x0D, 0,0,0,0, 0xE8};
        uint8_t msk[] = {1,1,1, 0,0,0,0, 1,0, 1,1,1, 0,0,0,0, 1};
        uint64_t hit = sig_scan(text_start, text_size, pat, msk, sizeof(pat));
        if (hit) {
            g_fname_pool = resolve_rip_relative(hit, 7);
            printf("[+] FNamePool: 0x%llX\n", (unsigned long long)g_fname_pool);
        } else {
            printf("[-] FNamePool sig failed\n");
        }
    }
 
    /* --- resolve game offsets via FProperty reflection --- */
    if (g_fname_pool) {
        /* need a live actor to get its UClass. walk: GWorld->Level->Actors[local_pawn] */
        uint64_t gworld = read64(g_base + g_off_gworld);
        uint64_t gi = gworld ? read64(gworld + 0x228) : 0;
        uint64_t lp = gi ? read64(read64(gi + 0x38)) : 0;
        uint64_t pc = lp ? read64(lp + 0x30) : 0;
        uint64_t pawn = pc ? read64(pc + 0x2E8) : 0;
 
        if (pawn) {
            uint64_t pawn_class = read64(pawn + UOBJECT_CLASS);
            if (pawn_class) {
                int32_t off;
                printf("[*] Resolving player offsets via reflection...\n");
                dump_properties(pawn_class, "PlayerPawn");
 
                if (find_property_offset(pawn_class, "Health", &off))
                    { g_off_player_health = off; printf("[+]   Health = 0x%X\n", off); }
                if (find_property_offset(pawn_class, "MaxHealthValue", &off))
                    { g_off_player_max_health = off; printf("[+]   MaxHealthValue = 0x%X\n", off); }
                if (find_property_offset(pawn_class, "Dead", &off))
                    { g_off_player_dead = off; printf("[+]   Dead = 0x%X\n", off); }
                if (find_property_offset(pawn_class, "Mesh", &off))
                    { g_off_player_mesh = off; printf("[+]   Mesh = 0x%X\n", off); }
                if (find_property_offset(pawn_class, "Difficulty", &off))
                    { g_off_player_difficulty = off; printf("[+]   Difficulty = 0x%X\n", off); }
                if (find_property_offset(pawn_class, "FirstMeshComponentTransform", &off))
                    { g_off_player_mesh_xform = off; printf("[+]   FirstMeshComponentTransform = 0x%X\n", off); }
                if (find_property_offset(pawn_class, "DefaultCapsuleHeight", &off))
                    { g_off_capsule_height = off; printf("[+]   DefaultCapsuleHeight = 0x%X\n", off); }

                /* try to find weapon/ammo */
                const char* weapon_props[] = {
                    "CurrentWeapon", "Weapon", "CurrentWeaponActor",
                    "EquippedWeapon", "HeldWeapon", "ActiveWeapon",
                    "WeaponActor"
                };
                for (int wp = 0; wp < 7; wp++) {
                    if (find_property_offset(pawn_class, weapon_props[wp], &off)) {
                        g_off_current_weapon = off;
                        printf("[+]   %s = 0x%X\n", weapon_props[wp], off);
                        break;
                    }
                }

                /* try to find ammo directly on pawn as fallback */
                const char* ammo_pawn_props[] = {
                    "Ammo", "CurrentAmmo", "Bullets",
                    "AmmoCount", "StoredAmmo"
                };
                for (int ap = 0; ap < 5 && !g_off_ammo_current; ap++) {
                    if (find_property_offset(pawn_class, ammo_pawn_props[ap], &off)) {
                        g_off_ammo_current = off;
                        printf("[+] Pawn::%s = 0x%X\n", ammo_pawn_props[ap], off);
                    }
                }
            }
        }

        /* resolve weapon ammo offsets if we have a weapon */
        if (g_off_current_weapon && pawn) {
            uint64_t weapon = read64(pawn + g_off_current_weapon);
            if (weapon) {
                uint64_t weapon_class = read64(weapon + UOBJECT_CLASS);
                if (weapon_class) {
                    int32_t off;
                    dump_properties(weapon_class, "Weapon");
                    const char* ammo_props[] = {
                        "CurrentAmmo", "Ammo", "Bullets", "AmmoCount",
                        "ClipSize", "AmmoInClip", "ClipAmmo", "RemainingAmmo",
                        "LoadedAmmo", "CurrentAmmoCount", "RoundsInClip"
                    };
                    for (int ap = 0; ap < 11; ap++) {
                        if (find_property_offset(weapon_class, ammo_props[ap], &off)) {
                            g_off_ammo_current = off;
                            printf("[+] Weapon::%s = 0x%X\n", ammo_props[ap], off);
                            break;
                        }
                    }
                    const char* max_ammo_props[] = {
                        "MaxAmmo", "MaxAmmoCount", "MaxBullets",
                        "ClipSize", "MaxRounds", "MaxAmmoInClip"
                    };
                    for (int ap = 0; ap < 6; ap++) {
                        if (find_property_offset(weapon_class, max_ammo_props[ap], &off)) {
                            g_off_ammo_max = off;
                            printf("[+] Weapon::%s = 0x%X\n", max_ammo_props[ap], off);
                            break;
                        }
                    }
                }
            }
        }

        /* if still no ammo offset, try scanning for uknown ammo via brute force */
        if (!g_off_ammo_current && g_fname_pool) {
            /* walk all components on the pawn to find anything weapon-like */
            printf("[*] Scanning pawn components for weapon...\n");
            /* iterate components using InternalComponents array */
            uint64_t comp_data = read64(pawn + 0x1C8);
            int32_t comp_count = read32(pawn + 0x1C8 + 8);
            if (comp_data && comp_count > 0 && comp_count < 200) {
                for (int ci = 0; ci < comp_count; ci++) {
                    uint64_t comp = read64(comp_data + (uint64_t)ci * 8);
                    if (!comp) continue;
                    uint64_t comp_class = read64(comp + UOBJECT_CLASS);
                    if (!comp_class) continue;
                    uint32_t cfid = read32(comp_class + FFIELD_NAME);
                    char cn[128];
                    if (fname_to_string(cfid, cn, sizeof(cn))) {
                        if (strstr(cn, "Weapon") || strstr(cn, "Inventory") ||
                            strstr(cn, "Equipment") || strstr(cn, "Ammo")) {
                            printf("[+] Found component: %s (0x%llX)\n", cn, (unsigned long long)comp);
                            /* try to find ammo properties on this component */
                            int32_t off;
                            const char* ammo_props[] = {"CurrentAmmo", "Ammo", "AmmoCount", "Bullets"};
                            for (int ap = 0; ap < 4; ap++) {
                                if (find_property_offset(comp_class, ammo_props[ap], &off)) {
                                    g_off_ammo_current = off;
                                    printf("[+] %s::%s = 0x%X\n", cn, ammo_props[ap], off);
                                    break;
                                }
                            }
                            if (g_off_ammo_current) break;
                        }
                    }
                }
            }
        }

        /* try to find Enemy_AI_Base offsets from a level actor */
        uint64_t level = gworld ? read64(gworld + 0x30) : 0;
        uint64_t actors_data = level ? read64(level + 0xA0) : 0;
        int32_t actors_count = level ? read32(level + 0xA8) : 0;
        if (actors_data && actors_count > 0) {
            for (int i = 0; i < actors_count && i < 500; i++) {
                uint64_t actor = read64(actors_data + i * 8);
                if (!actor || actor == pawn) continue;
                uint64_t actor_class = read64(actor + UOBJECT_CLASS);
                if (!actor_class) continue;
                /* check class name for Enemy_AI_Base */
                uint32_t class_fname = read32(actor_class + FFIELD_NAME);
                char cname[128];
                if (fname_to_string(class_fname, cname, sizeof(cname)) &&
                    strstr(cname, "Enemy_AI_Base")) {
                    int32_t off;
                    printf("[*] Found %s, resolving enemy offsets...\n", cname);
                    if (find_property_offset(actor_class, "Health", &off))
                        { g_off_enemy_health = off; printf("[+]   Health = 0x%X\n", off); }
                    if (find_property_offset(actor_class, "MaxHealth", &off))
                        { g_off_enemy_max_health = off; printf("[+]   MaxHealth = 0x%X\n", off); }
                    if (find_property_offset(actor_class, "IsDown", &off))
                        { g_off_enemy_is_down = off; printf("[+]   IsDown = 0x%X\n", off); }
                    break;
                }
            }
        }
    }
 
    return 1;
}
 
/* ── UE5.6.1 engine offsets (stable per engine version) ────── */
 
/* these only change when the game updates to a new UE version */
#define OFF_UWORLD_PERSISTENT_LEVEL    0x30
#define OFF_UWORLD_GAME_INSTANCE       0x228
#define OFF_ULEVEL_ACTORS              0xA0
#define OFF_ACTOR_ROOT_COMPONENT       0x1B8
#define OFF_SCENE_RELATIVE_LOCATION    0x140
#define OFF_COMPONENT_TO_WORLD         0x1E0  /* FTransform: quat(+0x00) pos(+0x20) scale(+0x40) */
#define OFF_GI_LOCAL_PLAYERS           0x38
#define OFF_PLAYER_CONTROLLER          0x30
#define OFF_PC_CAMERA_MANAGER          0x360
#define OFF_CONTROLLER_PAWN            0x2E8
#define OFF_CAM_CACHE                  0x1530
#define OFF_CACHE_POV                  0x10
#define OFF_POV_LOCATION               0x00
#define OFF_POV_ROTATION               0x18
#define OFF_POV_FOV                    0x30
 
/* Enemy_AI_Base_C (inherits ACharacter @ 0x650) */
#define OFF_ENEMY_HEALTH               0x8D8
#define OFF_ENEMY_MAX_HEALTH           0x908
#define OFF_ENEMY_IS_DOWN              0x8A8
 
/* BP_FirstPersonCharacter_Main_C (inherits APawn via MoverExamplesCharacter) */
#define OFF_PLAYER_HEALTH              0x640
#define OFF_PLAYER_MAX_HEALTH          0x648
#define OFF_PLAYER_DEAD                0x5AA
#define OFF_PLAYER_DIFFICULTY          0x624
#define OFF_MESH_TRANSFORM             0x900  /* FTransform FirstMeshComponentTransform -- scale at +0x40 */
 
/* UObject vtable sits at 0x0 -- class pointer at 0x10 */
#define OFF_UOBJECT_CLASS              0x10
 
/* Skeleton / bone data */
/* ACharacter::Mesh = 0x328, player BP_FirstPersonCharacter_Main_C::Mesh = 0x418 */
#define OFF_CHAR_MESH                  0x328  /* ACharacter -> USkeletalMeshComponent* */
#define OFF_PLAYER_MESH                0x418  /* BP_FirstPersonCharacter_Main_C -> Mesh */
 
/* USkinnedMeshComponent bone array (in Pad_5E0, runtime TArray<FTransform>) */
#define OFF_BONE_ARRAY                 0x5F0  /* TArray<FTransform> ComponentSpaceTransforms[0] */
#define OFF_BONE_ARRAY2                0x600  /* TArray<FTransform> ComponentSpaceTransforms[1] (double-buffered) */
 
/* FTransform layout (UE5 LWC -- all doubles) */
#define FTRANSFORM_SIZE                0x60   /* 96 bytes: quat(32) + pos(24) + scale(24) + pad(16) */
#define FTRANSFORM_POS_OFF             0x20   /* translation starts after FQuat (4 doubles) */
 
/* bone indices -- standard UE5 humanoid skeleton (28 bones) */
/* these are guesses for this game's skeleton; visually verify and adjust */
#define BONE_ROOT       0
#define BONE_PELVIS     1
#define BONE_SPINE1     2   /* z=53 */
#define BONE_SPINE2     3   /* z=65 */
#define BONE_SPINE3     4   /* z=79 */
#define BONE_CHEST      5   /* z=97 upper chest */
#define BONE_NECK       6   /* z=108 */
#define BONE_HEAD       7   /* z=130 */
#define BONE_CLAV_R     8
#define BONE_UPPER_R    9
#define BONE_LOWER_R    10
#define BONE_HAND_L     10
#define BONE_WRIST_R    11
#define BONE_HAND_R     12
#define BONE_CLAV_L     13
#define BONE_UPPER_L    14
#define BONE_LOWER_L    15
#define BONE_HAND_R     14
#define BONE_WRIST_L    16
#define BONE_HAND_L     17
#define BONE_THIGH_R    19
#define BONE_CALF_R     20
#define BONE_FOOT_R     21
#define BONE_THIGH_L    24
#define BONE_CALF_L     25
#define BONE_FOOT_L     26
#define BONE_COUNT_MAX  28
 
typedef struct { int from; int to; } BonePair;
static const BonePair g_bone_pairs[] = {
    /* spine (skip root/pelvis -- they're at mesh origin, not actual pelvis) */
    { BONE_SPINE1, BONE_SPINE2 },
    { BONE_SPINE2, BONE_SPINE3 },
    { BONE_SPINE3, BONE_CHEST },
    { BONE_CHEST,  BONE_NECK },
    { BONE_NECK,   BONE_HEAD },
    /* right arm */
    { BONE_CHEST,   BONE_CLAV_R },
    { BONE_CLAV_R,  BONE_UPPER_R },
    { BONE_UPPER_R, BONE_LOWER_R },
    { BONE_LOWER_R, BONE_WRIST_R },
    /* left arm */
    { BONE_CHEST,   BONE_CLAV_L },
    { BONE_CLAV_L,  BONE_UPPER_L },
    { BONE_UPPER_L, BONE_LOWER_L },
    { BONE_LOWER_L, BONE_WRIST_L },
    /* right leg */
    { BONE_SPINE1,  BONE_THIGH_R },
    { BONE_THIGH_R, BONE_CALF_R },
    { BONE_CALF_R,  BONE_FOOT_R },
    /* left leg */
    { BONE_SPINE1,  BONE_THIGH_L },
    { BONE_THIGH_L, BONE_CALF_L },
    { BONE_CALF_L,  BONE_FOOT_L },
};
#define BONE_PAIR_COUNT (sizeof(g_bone_pairs)/sizeof(g_bone_pairs[0]))
 
/* ── aimbot config ─────────────────────────────────────────── */
 
static int g_aim_key = VK_RBUTTON;
static int g_aim_key_binding = 0; /* 1 = waiting for keypress to rebind */
 
static const char* vk_name(int vk) {
    switch (vk) {
        case VK_LBUTTON: return "LMB";
        case VK_RBUTTON: return "RMB";
        case VK_MBUTTON: return "MMB";
        case VK_XBUTTON1: return "MB4";
        case VK_XBUTTON2: return "MB5";
        case VK_SHIFT: return "SHIFT";
        case VK_CONTROL: return "CTRL";
        case VK_MENU: return "ALT";
        case VK_CAPITAL: return "CAPS";
        case VK_TAB: return "TAB";
        case VK_SPACE: return "SPACE";
        default: {
            static char buf[8];
            if (vk >= 0x30 && vk <= 0x39) { buf[0] = (char)vk; buf[1] = 0; return buf; }
            if (vk >= 0x41 && vk <= 0x5A) { buf[0] = (char)vk; buf[1] = 0; return buf; }
            if (vk >= VK_F1 && vk <= VK_F12) { snprintf(buf, sizeof(buf), "F%d", vk - VK_F1 + 1); return buf; }
            snprintf(buf, sizeof(buf), "0x%02X", vk); return buf;
        }
    }
}
 
static int poll_any_key(void) {
    for (int vk = 1; vk < 256; vk++) {
        if (vk == VK_INSERT || vk == VK_ESCAPE) continue;
        if (GetAsyncKeyState(vk) & 1) return vk;
    }
    return 0;
}
 
typedef struct {
    float fov_radius;
    float smoothing_near;       /* high value = slow when close to target */
    float smoothing_far;        /* low value = fast when far from target */
    float dead_zone;
    float head_offset;
    float jitter_amplitude;     /* hand tremor magnitude (px) */
    float jitter_interval_ms;   /* tremor update frequency */
    float wander_radius;        /* slow drift around aim point (px) */
    float wander_interval_ms;
    float overshoot_chance;     /* probability per new target [0-1] */
    float overshoot_distance;   /* max overshoot (px) */
    float overshoot_decay_ms;   /* recovery time */
    float reaction_min_ms;
    float reaction_max_ms;
    float switch_cooldown_ms;   /* min time between target switches */
    float sticky_score_bonus;   /* score multiplier for locked target (<1 = prefer) */
    float sticky_fov_mult;      /* FOV multiplier to retain locked target */
    float distance_weight;      /* 3D distance contribution to target score */
    float crosshair_weight;     /* screen distance contribution to target score */
    float max_move_per_frame;   /* px cap to prevent snap */
    float velocity_inertia;     /* mouse momentum carry [0-1] */
    int   target_ai;
    int   target_players;
} AimConfig;
 
typedef struct {
    int      has_target;
    uint64_t locked_actor;
    DWORD    lock_time;
    DWORD    last_switch;
    int      miss_frames;
    int      in_reaction_delay;
    DWORD    reaction_end;
    float    jitter_x, jitter_y;
    float    jitter_goal_x, jitter_goal_y;
    DWORD    jitter_next;
    float    wander_x, wander_y;
    float    wander_goal_x, wander_goal_y;
    DWORD    wander_next;
    int      overshooting;
    float    overshoot_x, overshoot_y;
    DWORD    overshoot_end;
    float    vel_x, vel_y;
} AimState;
 
static AimConfig g_aim_cfg;
static AimState  g_aim_st;
 
typedef struct { double x, y, z; } Vec3;
typedef struct { double pitch, yaw, roll; } Rot3;
 
/* ── screen / overlay ──────────────────────────────────────── */
 
static int   g_screen_w = 1920;
static int   g_screen_h = 1080;
static HWND  g_overlay  = NULL;
static HWND  g_game_wnd = NULL;
 
#define OVERLAY_COLOR_KEY RGB(0, 0, 0)
#define MENU_KEY          VK_INSERT
#define MENU_WIDTH        300
#define MENU_HEADER_H     40
#define MENU_PADDING      10
#define MENU_ROW_H        26
#define MENU_ROW_GAP      4
 
/* menu item types */
#define MI_TOGGLE  0
#define MI_SLIDER  1
#define MI_KEYBIND 2

/* tab IDs */
#define TAB_AIMBOT 0
#define TAB_VISUAL 1
#define TAB_GODMODE 2
#define TAB_MISC 3
#define TAB_COUNT  4
#define TAB_WIDTH  60

static const char* g_tab_names[TAB_COUNT] = {"AIM", "ESP", "GOD", "MISC"};

typedef struct {
    const char* label;
    int         type;     /* MI_TOGGLE or MI_SLIDER */
    int*        toggle;   /* for MI_TOGGLE */
    float*      value;    /* for MI_SLIDER */
    float       min_val, max_val;
    int         tab;      /* TAB_AIMBOT, TAB_VISUAL, etc. */
} MenuItem;
 
typedef struct {
    int is_open;
    int is_dragging;
    int dragging_slider; /* index of slider being dragged, -1 if none */
    int hover_item_index;
    int x, y;
    int drag_offset_x, drag_offset_y;
    int esp_enabled;
    int aim_enabled;
    int show_ai;
    int show_players;
    int show_boxes;
    int show_health;
    int show_labels;
    int show_snaplines;
    int show_fov_circle;
    int enemy_only;
    int ammo_infinite;
    int god_mode;
    int rage_mode;
    int current_tab;
    int invisible;
    int noclip;
    int speed_boost;
} MenuState;

static float g_speed_value = 600.0f;
 
static MenuState g_menu = {
    .is_open = 0,
    .dragging_slider = -1,
    .hover_item_index = -1,
    .x = 32, .y = 72,
    .esp_enabled = 1,
    .aim_enabled = 1,
    .show_ai = 0,
    .show_players = 1,
    .show_boxes = 1,
    .show_health = 1,
    .show_labels = 1,
    .show_snaplines = 1,
    .show_fov_circle = 1,
    .enemy_only = 1,
    .ammo_infinite = 0,
    .god_mode = 0,
    .rage_mode = 0,
    .current_tab = 0,
    .invisible = 0,
    .noclip = 0,
    .speed_boost = 0
};
 
static MenuItem g_menu_items[20];
static int      g_menu_item_count = 0;

static void init_menu_items(void) {
    int i = 0;
    g_menu_items[i++] = (MenuItem){"Aimbot",       MI_TOGGLE, &g_menu.aim_enabled,    NULL, 0,0, TAB_AIMBOT};
    g_menu_items[i++] = (MenuItem){"Aim FOV",      MI_SLIDER, NULL, &g_aim_cfg.fov_radius, 20, 400, TAB_AIMBOT};
    g_menu_items[i++] = (MenuItem){"Aim Speed",    MI_SLIDER, NULL, &g_aim_cfg.smoothing_far, 1, 20, TAB_AIMBOT};
    g_menu_items[i++] = (MenuItem){"Aim Key",      MI_KEYBIND, NULL, NULL, 0, 0, TAB_AIMBOT};
    g_menu_items[i++] = (MenuItem){"FOV Circle",   MI_TOGGLE, &g_menu.show_fov_circle,NULL, 0,0, TAB_AIMBOT};
    g_menu_items[i++] = (MenuItem){"ESP",          MI_TOGGLE, &g_menu.esp_enabled,    NULL, 0,0, TAB_VISUAL};
    g_menu_items[i++] = (MenuItem){"Boxes",        MI_TOGGLE, &g_menu.show_boxes,     NULL, 0,0, TAB_VISUAL};
    g_menu_items[i++] = (MenuItem){"Health Bars",  MI_TOGGLE, &g_menu.show_health,    NULL, 0,0, TAB_VISUAL};
    g_menu_items[i++] = (MenuItem){"Labels",       MI_TOGGLE, &g_menu.show_labels,    NULL, 0,0, TAB_VISUAL};
    g_menu_items[i++] = (MenuItem){"Show Players", MI_TOGGLE, &g_menu.show_players,   NULL, 0,0, TAB_VISUAL};
    g_menu_items[i++] = (MenuItem){"Show AI",      MI_TOGGLE, &g_menu.show_ai,        NULL, 0,0, TAB_VISUAL};
    g_menu_items[i++] = (MenuItem){"Enemy Only",   MI_TOGGLE, &g_menu.enemy_only,     NULL, 0,0, TAB_VISUAL};
    g_menu_items[i++] = (MenuItem){"God Mode",     MI_TOGGLE, &g_menu.god_mode,       NULL, 0,0, TAB_GODMODE};
    g_menu_items[i++] = (MenuItem){"Invisible",    MI_TOGGLE, &g_menu.invisible,      NULL, 0,0, TAB_GODMODE};
    g_menu_items[i++] = (MenuItem){"NoClip",       MI_TOGGLE, &g_menu.noclip,         NULL, 0,0, TAB_GODMODE};
    g_menu_items[i++] = (MenuItem){"Inf Ammo",     MI_TOGGLE, &g_menu.ammo_infinite,  NULL, 0,0, TAB_MISC};
    g_menu_items[i++] = (MenuItem){"Rage Mode",    MI_TOGGLE, &g_menu.rage_mode,      NULL, 0,0, TAB_MISC};
    g_menu_items[i++] = (MenuItem){"Speed",        MI_SLIDER, NULL, &g_speed_value, 100, 3000, TAB_MISC};
    g_menu_item_count = i;
}
 
static int get_menu_height(void) {
    int tab_h = TAB_COUNT * 60 + 10;
    int vis_items = 0;
    for (int i = 0; i < g_menu_item_count; i++)
        if (g_menu_items[i].tab == g_menu.current_tab) vis_items++;
    int items_h = MENU_PADDING * 2 + vis_items * (MENU_ROW_H + MENU_ROW_GAP);
    return MENU_HEADER_H + (tab_h > items_h ? tab_h : items_h) + 4;
}
 
static int   g_last_enemy_count = 0;
static int   g_last_player_count = 0;
static float g_last_camera_fov = 90.0f;
static int   g_overlay_is_interactive = 0;
static int   g_overlay_is_visible = 1;
 
static RECT get_menu_bounds(void);
static RECT get_menu_header_bounds(void);
static RECT get_menu_close_bounds(void);
static RECT get_menu_item_bounds(int item_index);
static int is_point_inside_rect(POINT point, RECT rect);
static int get_menu_item_index_at_point(POINT point);
static void clamp_menu_position_to_overlay(void);
static void toggle_menu_item(int item_index);
static void handle_menu_mouse_down(HWND wnd, int x, int y);
static void handle_menu_mouse_move(int x, int y);
static void handle_menu_mouse_up(HWND wnd);
static int is_game_foreground(void);
static void set_overlay_interactive(int should_be_interactive);
static void set_overlay_visible(int should_be_visible);
static void handle_hotkeys(void);
/* ── menu implementation ────────────────────────────────────── */
 
static RECT get_menu_item_bounds(int vis_idx) {
    int y = g_menu.y + MENU_HEADER_H + MENU_PADDING + vis_idx * (MENU_ROW_H + MENU_ROW_GAP);
    RECT r = { g_menu.x + TAB_WIDTH + 8, y, g_menu.x + MENU_WIDTH - 8, y + MENU_ROW_H };
    return r;
}

static int pt_in_rect(int px, int py, RECT r) {
    return px >= r.left && px <= r.right && py >= r.top && py <= r.bottom;
}

static int get_item_at(int px, int py) {
    int vis_idx = 0;
    for (int i = 0; i < g_menu_item_count; i++) {
        if (g_menu_items[i].tab != g_menu.current_tab) continue;
        RECT r = get_menu_item_bounds(vis_idx);
        if (pt_in_rect(px, py, r)) return i;
        vis_idx++;
    }
    return -1;
}
 
static void clamp_menu_pos(void) {
    if (g_menu.x < 0) g_menu.x = 0;
    if (g_menu.y < 0) g_menu.y = 0;
    if (g_menu.x + MENU_WIDTH > g_screen_w) g_menu.x = g_screen_w - MENU_WIDTH;
    int mh = get_menu_height();
    if (g_menu.y + mh > g_screen_h) g_menu.y = g_screen_h - mh;
}
 
static int get_tab_visible_index(int item_idx) {
    int vis = 0;
    for (int i = 0; i < item_idx; i++) {
        if (g_menu_items[i].tab == g_menu_items[item_idx].tab) vis++;
    }
    return vis;
}

static int get_tab_at(int px, int py) {
    for (int t = 0; t < TAB_COUNT; t++) {
        int tx = g_menu.x + 4;
        int ty = g_menu.y + MENU_HEADER_H + 10 + t * 60;
        if (px >= tx && px <= tx + TAB_WIDTH - 8 && py >= ty && py <= ty + 50)
            return t;
    }
    return -1;
}

static RECT get_slider_track(int idx) {
    int vis_idx = get_tab_visible_index(idx);
    RECT item = get_menu_item_bounds(vis_idx);
    int sl = item.left + 100, sr = item.right - 50;
    int sy = item.top + MENU_ROW_H / 2 - 3;
    RECT r = { sl, sy, sr, sy + 6 };
    return r;
}
 
static void update_slider(int idx, int mouse_x) {
    if (idx < 0 || idx >= g_menu_item_count) return;
    MenuItem* mi = &g_menu_items[idx];
    if (mi->type != MI_SLIDER || !mi->value) return;
    RECT track = get_slider_track(idx);
    float t = (float)(mouse_x - track.left) / (float)(track.right - track.left);
    if (t < 0) t = 0; if (t > 1) t = 1;
    *mi->value = mi->min_val + t * (mi->max_val - mi->min_val);
}
 
static void handle_menu_mouse_down(HWND wnd, int x, int y) {
    /* tab click */
    int tab = get_tab_at(x, y);
    if (tab >= 0) {
        g_menu.current_tab = tab;
        return;
    }
    /* close button */
    RECT cls = { g_menu.x + MENU_WIDTH - 28, g_menu.y + 6, g_menu.x + MENU_WIDTH - 6, g_menu.y + 28 };
    if (pt_in_rect(x, y, cls)) {
        g_menu.is_open = 0;
        set_overlay_interactive(0);
        return;
    }
    /* header drag */
    RECT hdr = { g_menu.x, g_menu.y, g_menu.x + MENU_WIDTH, g_menu.y + MENU_HEADER_H };
    if (pt_in_rect(x, y, hdr)) {
        g_menu.is_dragging = 1;
        g_menu.drag_offset_x = x - g_menu.x;
        g_menu.drag_offset_y = y - g_menu.y;
        return;
    }
    int idx = get_item_at(x, y);
    if (idx >= 0) {
        MenuItem* mi = &g_menu_items[idx];
        if (mi->type == MI_TOGGLE && mi->toggle)
            *mi->toggle = !*mi->toggle;
        else if (mi->type == MI_KEYBIND)
            g_aim_key_binding = 1;
        else if (mi->type == MI_SLIDER) {
            g_menu.dragging_slider = idx;
            update_slider(idx, x);
        }
    }
}
 
static void handle_menu_mouse_move(int x, int y) {
    if (g_menu.is_dragging) {
        g_menu.x = x - g_menu.drag_offset_x;
        g_menu.y = y - g_menu.drag_offset_y;
        clamp_menu_pos();
    }
    if (g_menu.dragging_slider >= 0)
        update_slider(g_menu.dragging_slider, x);
    g_menu.hover_item_index = get_item_at(x, y);
}
 
static void handle_menu_mouse_up(HWND wnd) {
    (void)wnd;
    g_menu.is_dragging = 0;
    g_menu.dragging_slider = -1;
}
 
static int is_game_foreground(void) {
    HWND fg = GetForegroundWindow();
    if (fg == g_game_wnd || fg == g_overlay) return 1;
    /* also check by PID -- game may have multiple windows */
    DWORD fg_pid = 0;
    GetWindowThreadProcessId(fg, &fg_pid);
    return (fg_pid == g_pid);
}
 
static void set_overlay_interactive(int interactive) {
    if (interactive == g_overlay_is_interactive) return;
    g_overlay_is_interactive = interactive;
    LONG ex = GetWindowLongA(g_overlay, GWL_EXSTYLE);
    if (interactive)
        ex &= ~WS_EX_TRANSPARENT;
    else
        ex |= WS_EX_TRANSPARENT;
    SetWindowLongA(g_overlay, GWL_EXSTYLE, ex);
}
 
static void set_overlay_visible(int vis) {
    if (vis == g_overlay_is_visible) return;
    g_overlay_is_visible = vis;
    ShowWindow(g_overlay, vis ? SW_SHOW : SW_HIDE);
}
 
static void handle_hotkeys(void) {
    /* keybind capture mode */
    if (g_aim_key_binding) {
        int vk = poll_any_key();
        if (vk) {
            g_aim_key = vk;
            g_aim_key_binding = 0;
        }
        return;
    }
    if (GetAsyncKeyState(MENU_KEY) & 1) {
        g_menu.is_open = !g_menu.is_open;
        set_overlay_interactive(g_menu.is_open);
    }
}
 
static void fill_rect_c(HDC h, int x, int y, int w, int ht, COLORREF c) {
    HBRUSH b = CreateSolidBrush(c);
    RECT r = {x, y, x+w, y+ht};
    FillRect(h, &r, b);
    DeleteObject(b);
}
 
static void draw_rounded_rect(HDC hdc, int x, int y, int w, int h, int r, COLORREF fill) {
    HBRUSH b = CreateSolidBrush(fill);
    SelectObject(hdc, b);
    SelectObject(hdc, GetStockObject(NULL_PEN));
    RoundRect(hdc, x, y, x+w, y+h, r*2, r*2);
    DeleteObject(b);
}

static void draw_menu(HDC hdc) {
    if (!g_menu.is_open) return;
    int mx = g_menu.x, my = g_menu.y;
    int mh = get_menu_height();
    int mw = MENU_WIDTH;

    SetBkMode(hdc, TRANSPARENT);

    /* shadow */
    fill_rect_c(hdc, mx+3, my+3, mw, mh, RGB(0,0,0));

    /* main bg */
    fill_rect_c(hdc, mx, my, mw, mh, RGB(12,12,15));

    /* header bg */
    fill_rect_c(hdc, mx, my, mw, MENU_HEADER_H, RGB(18,18,24));

    /* header accent line */
    fill_rect_c(hdc, mx+15, my+MENU_HEADER_H-1, mw-30, 1, RGB(40,130,255));

    HFONT title_f = CreateFontA(14, 0,0,0, FW_HEAVY, 0,0,0,
                                DEFAULT_CHARSET,0,0,CLEARTYPE_QUALITY,
                                DEFAULT_PITCH, "Segoe UI");
    HFONT tab_f = CreateFontA(11, 0,0,0, FW_BOLD, 0,0,0,
                               DEFAULT_CHARSET,0,0,CLEARTYPE_QUALITY,
                               DEFAULT_PITCH, "Segoe UI");
    HFONT item_f = CreateFontA(12, 0,0,0, FW_SEMIBOLD, 0,0,0,
                               DEFAULT_CHARSET,0,0,CLEARTYPE_QUALITY,
                               DEFAULT_PITCH, "Segoe UI");
    HFONT item_val_f = CreateFontA(11, 0,0,0, FW_BOLD, 0,0,0,
                                   DEFAULT_CHARSET,0,0,CLEARTYPE_QUALITY,
                                   DEFAULT_PITCH, "Segoe UI");

    /* title */
    SelectObject(hdc, title_f);
    SetTextColor(hdc, RGB(230, 230, 240));
    TextOutA(hdc, mx+14, my+11, "FENIX V1", 8);

    /* close */
    SelectObject(hdc, item_f);
    SetTextColor(hdc, RGB(60,60,70));
    TextOutA(hdc, mx+mw-18, my+12, "x", 1);

    /* separator line below header */
    HPEN sep = CreatePen(PS_SOLID, 1, RGB(25,25,35));
    SelectObject(hdc, sep);
    MoveToEx(hdc, mx, my+MENU_HEADER_H, NULL);
    LineTo(hdc, mx+mw, my+MENU_HEADER_H);

    /* ── left tab buttons ── */
    HPEN tab_active_pen = CreatePen(PS_SOLID, 1, RGB(40,130,255));
    HPEN tab_inactive_pen = CreatePen(PS_SOLID, 1, RGB(25,25,35));
    SelectObject(hdc, tab_f);

    for (int t = 0; t < TAB_COUNT; t++) {
        int tx = mx + 8;
        int ty = my + MENU_HEADER_H + 8 + t * 56;
        int tw = TAB_WIDTH - 16;
        int th = 46;
        int is_active = (t == g_menu.current_tab);
        int is_hover = 0;

        /* tab bg */
        fill_rect_c(hdc, tx, ty, tw, th, is_active ? RGB(22,20,30) : RGB(13,13,16));
        /* left accent when active */
        if (is_active)
            fill_rect_c(hdc, tx, ty+4, 2, th-8, RGB(40,130,255));

        SetTextColor(hdc, is_active ? RGB(200,180,240) : RGB(90,90,100));
        int tlen = (int)strlen(g_tab_names[t]);
        TextOutA(hdc, tx + (tw - tlen*7)/2, ty + (th - 8)/2, g_tab_names[t], tlen);
    }

    /* separator line between tabs and items */
    MoveToEx(hdc, mx + TAB_WIDTH, my + MENU_HEADER_H, NULL);
    LineTo(hdc, mx + TAB_WIDTH, my + mh - 4);
    DeleteObject(tab_active_pen);
    DeleteObject(tab_inactive_pen);

    /* ── right panel items ── */
    SelectObject(hdc, item_f);
    int vis_idx = 0;

    for (int i = 0; i < g_menu_item_count; i++) {
        MenuItem* mi = &g_menu_items[i];
        if (mi->tab != g_menu.current_tab) continue;

        RECT item = get_menu_item_bounds(vis_idx);
        int hovered = (i == g_menu.hover_item_index);
        int iw = item.right - item.left;
        int ih = item.bottom - item.top;

        /* row bg */
        if (hovered)
            fill_rect_c(hdc, item.left, item.top, iw, ih, RGB(20,20,28));

        /* left accent on hover */
        if (hovered)
            fill_rect_c(hdc, item.left, item.top+3, 3, ih-6, RGB(40,130,255));

        /* label */
        SetTextColor(hdc, hovered ? RGB(230,230,240) : RGB(140,140,150));
        TextOutA(hdc, item.left+12, item.top+5, mi->label, (int)strlen(mi->label));

        if (mi->type == MI_TOGGLE) {
            int on = mi->toggle ? *mi->toggle : 0;
            int tw = 28, th = 14;
            int tx = item.right - tw - 8;
            int ty = item.top + (MENU_ROW_H - th) / 2;

            /* track */
            fill_rect_c(hdc, tx, ty, tw, th, on ? RGB(40,130,255) : RGB(30,30,38));

            /* knob */
            int kx = on ? tx + tw - th + 1 : tx + 1;
            fill_rect_c(hdc, kx+1, ty+1, th-3, th-2, on ? RGB(250,250,255) : RGB(70,70,80));

        } else if (mi->type == MI_SLIDER && mi->value) {
            RECT track = get_slider_track(i);
            int tw = track.right - track.left;
            float t = (*mi->value - mi->min_val) / (mi->max_val - mi->min_val);
            if (t < 0) t = 0; if (t > 1) t = 1;
            int fill_w = (int)(tw * t);

            /* track */
            fill_rect_c(hdc, track.left, track.top, tw, 4, RGB(25,25,32));
            /* fill */
            fill_rect_c(hdc, track.left, track.top, fill_w, 4, RGB(40,130,255));
            /* handle */
            int hx = track.left + fill_w - 3;
            if (hx < track.left) hx = track.left;
            fill_rect_c(hdc, hx, track.top-4, 6, 12, hovered ? RGB(160,200,255) : RGB(180,170,210));

            /* value */
            char vbuf[16];
            snprintf(vbuf, sizeof(vbuf), "%.0f", *mi->value);
            SelectObject(hdc, item_val_f);
            SetTextColor(hdc, RGB(40,130,255));
            int vlen = (int)strlen(vbuf);
            TextOutA(hdc, item.right - 8 - vlen*6, item.top+5, vbuf, vlen);
            SelectObject(hdc, item_f);

        } else if (mi->type == MI_KEYBIND) {
            const char* label = g_aim_key_binding ? "[...]" : vk_name(g_aim_key);
            int llen = (int)strlen(label);
            int bw = llen * 7 + 12, bh = 18;
            int bx2 = item.right - bw - 6;
            int by2 = item.top + (MENU_ROW_H - bh) / 2;
            fill_rect_c(hdc, bx2, by2, bw, bh,
                        g_aim_key_binding ? RGB(40,130,255) : RGB(28,28,35));
            SetTextColor(hdc, g_aim_key_binding ? RGB(240,230,255) : RGB(140,120,190));
            TextOutA(hdc, bx2 + 6, by2 + 2, label, llen);
        }

        vis_idx++;
    }

    /* outer border */
    HPEN brd = CreatePen(PS_SOLID, 1, RGB(30,30,40));
    SelectObject(hdc, brd);
    SelectObject(hdc, GetStockObject(NULL_BRUSH));
    Rectangle(hdc, mx, my, mx+mw, my+mh);
    DeleteObject(brd);
    DeleteObject(sep);

    DeleteObject(title_f);
    DeleteObject(tab_f);
    DeleteObject(item_f);
    DeleteObject(item_val_f);
}
 
static void draw_status_hud(HDC hdc) {
    /* minimal top-left status when menu is closed */
}
 
/* persistent GDI resources (created once, not per-frame) */
static HFONT g_font      = NULL;
static HFONT g_menu_font = NULL;
static HFONT g_menu_title_font = NULL;
static HFONT g_menu_small_font = NULL;
static HPEN  g_red_pen   = NULL;
static HPEN  g_green_pen = NULL;
static HPEN  g_yellow_pen= NULL;
static HPEN  g_cyan_pen  = NULL;
static HPEN  g_snap_pen  = NULL;
static HPEN  g_fov_pen   = NULL;
 
static void create_gdi_resources(void) {
    g_font       = CreateFontA(14, 0, 0, 0, FW_BOLD, 0,0,0,
                               DEFAULT_CHARSET,0,0, ANTIALIASED_QUALITY,
                               DEFAULT_PITCH, "Consolas");
    g_menu_font  = CreateFontA(15, 0, 0, 0, FW_SEMIBOLD, 0,0,0,
                               DEFAULT_CHARSET,0,0, CLEARTYPE_QUALITY,
                               DEFAULT_PITCH, "Segoe UI");
    g_menu_title_font = CreateFontA(24, 0, 0, 0, FW_HEAVY, 0,0,0,
                                    DEFAULT_CHARSET,0,0, CLEARTYPE_QUALITY,
                                    DEFAULT_PITCH, "Bahnschrift SemiBold");
    g_menu_small_font = CreateFontA(12, 0, 0, 0, FW_SEMIBOLD, 0,0,0,
                                    DEFAULT_CHARSET,0,0, CLEARTYPE_QUALITY,
                                    DEFAULT_PITCH, "Segoe UI");
    g_red_pen    = CreatePen(PS_SOLID, 1, RGB(200, 60, 80));
    g_green_pen  = CreatePen(PS_SOLID, 1, RGB(80, 200, 120));
    g_yellow_pen = CreatePen(PS_SOLID, 1, RGB(200, 180, 60));
    g_cyan_pen   = CreatePen(PS_SOLID, 1, RGB(130, 100, 220));
    g_snap_pen   = CreatePen(PS_SOLID, 1, RGB(60, 60, 80));
    g_fov_pen    = CreatePen(PS_SOLID, 1, RGB(50, 50, 60));
}
 
static void destroy_gdi_resources(void) {
    if (g_font)       DeleteObject(g_font);
    if (g_menu_font)  DeleteObject(g_menu_font);
    if (g_menu_title_font) DeleteObject(g_menu_title_font);
    if (g_menu_small_font) DeleteObject(g_menu_small_font);
    if (g_red_pen)    DeleteObject(g_red_pen);
    if (g_green_pen)  DeleteObject(g_green_pen);
    if (g_yellow_pen) DeleteObject(g_yellow_pen);
    if (g_cyan_pen)   DeleteObject(g_cyan_pen);
    if (g_snap_pen)   DeleteObject(g_snap_pen);
    if (g_fov_pen)    DeleteObject(g_fov_pen);
}
 
/* ── math ──────────────────────────────────────────────────── */
 
#define PI 3.14159265358979323846
#define DEG2RAD(x) ((x) * PI / 180.0)
 
static int world_to_screen(Vec3 world, Vec3 cam_loc, Rot3 cam_rot, float fov,
                           float* sx, float* sy) {
    double sp, cp, sy_, cy, sr, cr;
    double fwd[3], right[3], up[3];
    double dx, dy, dz, w, x, y;
    double half_fov_tan, cx_d, cy_d;
 
    sp = sin(DEG2RAD(cam_rot.pitch));
    cp = cos(DEG2RAD(cam_rot.pitch));
    sy_= sin(DEG2RAD(cam_rot.yaw));
    cy = cos(DEG2RAD(cam_rot.yaw));
    sr = sin(DEG2RAD(cam_rot.roll));
    cr = cos(DEG2RAD(cam_rot.roll));
 
    fwd[0]   = cp * cy;
    fwd[1]   = cp * sy_;
    fwd[2]   = sp;
 
    right[0] = sr * sp * cy - cr * sy_;
    right[1] = sr * sp * sy_ + cr * cy;
    right[2] = -sr * cp;
 
    up[0]    = -(cr * sp * cy + sr * sy_);
    up[1]    = cy * sr - cr * sp * sy_;
    up[2]    = cr * cp;
 
    dx = world.x - cam_loc.x;
    dy = world.y - cam_loc.y;
    dz = world.z - cam_loc.z;
 
    w = dx * fwd[0]   + dy * fwd[1]   + dz * fwd[2];
    if (w < 1.0) return 0;
 
    x = dx * right[0] + dy * right[1] + dz * right[2];
    y = dx * up[0]    + dy * up[1]    + dz * up[2];
 
    half_fov_tan = tan(DEG2RAD(fov) / 2.0);
    cx_d = g_screen_w / 2.0;
    cy_d = g_screen_h / 2.0;
 
    *sx = (float)(cx_d + (x / w / half_fov_tan) * cx_d);
    *sy = (float)(cy_d - (y / w / half_fov_tan) * cx_d);
 
    return (*sx >= -500 && *sx <= g_screen_w + 500 &&
            *sy >= -500 && *sy <= g_screen_h + 500);
}
 
/* ── draw helpers ──────────────────────────────────────────── */
 
static void draw_text(HDC hdc, int x, int y, COLORREF col, const char* txt) {
    SetTextColor(hdc, col);
    SetBkMode(hdc, TRANSPARENT);
    TextOutA(hdc, x, y, txt, (int)strlen(txt));
}
 
static void draw_text_shadow(HDC hdc, int x, int y, COLORREF col, const char* txt) {
    draw_text(hdc, x+1, y+1, RGB(0,0,0), txt);
    draw_text(hdc, x, y, col, txt);
}
 
static void draw_box(HDC hdc, HPEN pen, int x, int y, int w, int h) {
    SelectObject(hdc, pen);
    SelectObject(hdc, GetStockObject(NULL_BRUSH));
    Rectangle(hdc, x, y, x + w, y + h);
}
 
static void draw_line(HDC hdc, HPEN pen, int x1, int y1, int x2, int y2) {
    SelectObject(hdc, pen);
    MoveToEx(hdc, x1, y1, NULL);
    LineTo(hdc, x2, y2);
}
 
static void draw_health_bar(HDC hdc, int x, int y, int w, int h,
                            double hp, double max_hp) {
    HBRUSH bg, fill;
    RECT rc;
    double ratio;
    int fill_h;
    COLORREF col;
 
    if (max_hp <= 0) return;
    ratio = hp / max_hp;
    if (ratio < 0) ratio = 0;
    if (ratio > 1) ratio = 1;
    fill_h = (int)(h * ratio);
 
    bg = CreateSolidBrush(RGB(20, 20, 20));
    rc.left = x; rc.top = y; rc.right = x + w; rc.bottom = y + h;
    FillRect(hdc, &rc, bg);
    DeleteObject(bg);
 
    if      (ratio > 0.6)  col = RGB(0, 255, 0);
    else if (ratio > 0.3)  col = RGB(255, 200, 0);
    else                   col = RGB(255, 0, 0);
 
    fill = CreateSolidBrush(col);
    rc.top = y + (h - fill_h);
    FillRect(hdc, &rc, fill);
    DeleteObject(fill);
}
 
/* ── cornered box (looks cleaner than full rectangle) ──────── */
 
static void draw_corner_box(HDC hdc, HPEN pen, int x, int y, int w, int h) {
    int corner = w / 3;
    if (corner < 5) corner = 5;
    SelectObject(hdc, pen);
 
    /* top-left */
    MoveToEx(hdc, x, y + corner, NULL); LineTo(hdc, x, y); LineTo(hdc, x + corner, y);
    /* top-right */
    MoveToEx(hdc, x+w-corner, y, NULL); LineTo(hdc, x+w, y); LineTo(hdc, x+w, y+corner);
    /* bot-left */
    MoveToEx(hdc, x, y+h-corner, NULL); LineTo(hdc, x, y+h); LineTo(hdc, x+corner, y+h);
    /* bot-right */
    MoveToEx(hdc, x+w-corner, y+h, NULL); LineTo(hdc, x+w, y+h); LineTo(hdc, x+w, y+h-corner);
}
 
/* ── find window / PID ─────────────────────────────────────── */
 
static BOOL CALLBACK find_game_cb(HWND hwnd, LPARAM lp) {
    DWORD pid;
    GetWindowThreadProcessId(hwnd, &pid);
    if (pid == g_pid && IsWindowVisible(hwnd)) {
        char t[256];
        GetWindowTextA(hwnd, t, sizeof(t));
        if (strlen(t) > 0) { *(HWND*)lp = hwnd; return FALSE; }
    }
    return TRUE;
}
 
static HWND find_game_window(void) {
    HWND w = NULL;
    EnumWindows(find_game_cb, (LPARAM)&w);
    return w;
}
 
static DWORD find_pid(const char* name) {
    HANDLE snap = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0);
    if (snap == INVALID_HANDLE_VALUE) return 0;
    PROCESSENTRY32 pe = { .dwSize = sizeof(pe) };
    DWORD pid = 0;
    if (Process32First(snap, &pe)) {
        do {
            if (_stricmp(pe.szExeFile, name) == 0) { pid = pe.th32ProcessID; break; }
        } while (Process32Next(snap, &pe));
    }
    CloseHandle(snap);
    return pid;
}
 
/* ── overlay wndproc ───────────────────────────────────────── */
 
static LRESULT CALLBACK overlay_proc(HWND wnd, UINT msg, WPARAM wp, LPARAM lp) {
    if (msg == WM_DESTROY) { PostQuitMessage(0); return 0; }
    if (msg == WM_PAINT) { PAINTSTRUCT ps; BeginPaint(wnd,&ps); EndPaint(wnd,&ps); return 0; }
    if (g_menu.is_open) {
        if (msg == WM_LBUTTONDOWN) {
            handle_menu_mouse_down(wnd, GET_X_LPARAM(lp), GET_Y_LPARAM(lp));
            return 0;
        }
        if (msg == WM_MOUSEMOVE) {
            handle_menu_mouse_move(GET_X_LPARAM(lp), GET_Y_LPARAM(lp));
            return 0;
        }
        if (msg == WM_LBUTTONUP) {
            handle_menu_mouse_up(wnd);
            return 0;
        }
    }
    return DefWindowProcA(wnd, msg, wp, lp);
}
 
/* ── sync overlay to game window ───────────────────────────── */
 
static void sync_overlay_to_game(void) {
    RECT rc;
    if (!g_game_wnd || !IsWindow(g_game_wnd)) {
        g_game_wnd = find_game_window();
        if (!g_game_wnd) return;
    }
    GetWindowRect(g_game_wnd, &rc);
    int w = rc.right - rc.left;
    int h = rc.bottom - rc.top;
    if (w != g_screen_w || h != g_screen_h || rc.left != 0 || rc.top != 0) {
        MoveWindow(g_overlay, rc.left, rc.top, w, h, TRUE);
    }
    RECT client;
    GetClientRect(g_game_wnd, &client);
    g_screen_w = client.right;
    g_screen_h = client.bottom;
}
 
/* ── entity type enum ──────────────────────────────────────── */
 
typedef enum {
    ENT_NONE,
    ENT_ENEMY_AI,
    ENT_PLAYER
} EntType;
 
#define OFF_PAWN_PLAYER_STATE    0x2C8
#define OFF_PS_PLAYER_NAME      0x340
 
typedef struct {
    Vec3     pos;
    double   hp;
    double   max_hp;
    double   dist;
    uint8_t  is_down;
    uint8_t  is_hunter;
    EntType  type;
    uint64_t mesh_comp;
    char     name[32];
} EntInfo;
 
/* try to classify an actor and read its health/position */
static int try_read_entity(uint64_t actor, uint64_t local_pawn,
                           Vec3 cam_loc, EntInfo* out) {
    double hp, max_hp;
    uint64_t root;
    Vec3 pos;
    double dx, dy, dz, dist;
 
    if (!actor || actor == local_pawn) return 0;
 
    /* quick validity: vtable must be a non-null aligned pointer in user space */
    uint64_t vt = read64(actor);
    if (!vt || vt < 0x10000ULL || vt > 0x7FFFFFFFFFFF || (vt & 7)) return 0;

    /* class name filter: reject if not a character/pawn/enemy */
    if (g_fname_pool) {
        uint64_t cls = read64(actor + UOBJECT_CLASS);
        uint32_t cls_fid = cls ? read32(cls + 0x18) : 0;
        char cn[128];
        if (fname_to_string(cls_fid, cn, sizeof(cn))) {
            int ok = 0;
            const char* valid_classes[] = {
                "Character", "Pawn", "Enemy", "AI_", "Player",
                "Chameleon", "Mover", "NPC"
            };
            for (int ci = 0; ci < 7; ci++) {
                if (strstr(cn, valid_classes[ci])) { ok = 1; break; }
            }
            if (!ok) return 0;
        }
    }

    /* try Enemy_AI_Base_C offsets first */
    max_hp = readd(actor + g_off_enemy_max_health);
    hp     = readd(actor + g_off_enemy_health);
 
    if (max_hp >= 1.0 && max_hp <= 50000.0 && hp >= 0.0 && hp <= max_hp + 1.0) {
        out->type = ENT_ENEMY_AI;
        out->hp = hp;
        out->max_hp = max_hp;
        out->is_down = read8(actor + g_off_enemy_is_down);
    } else {
        /* try player character offsets */
        max_hp = readd(actor + g_off_player_max_health);
        hp     = readd(actor + g_off_player_health);
 
        if (max_hp >= 1.0 && max_hp <= 50000.0 && hp >= 0.0 && hp <= max_hp + 1.0) {
            out->type = ENT_PLAYER;
            out->hp = hp;
            out->max_hp = max_hp;
            out->is_down = (hp <= 0.0) ? 1 : 0;
            /* check class name for team (Hunter vs not) */
            if (g_fname_pool) {
                uint64_t cls = read64(actor + UOBJECT_CLASS);
                uint32_t cls_fid = cls ? read32(cls + 0x18) : 0;
                char cn[128];
                out->is_hunter = (fname_to_string(cls_fid, cn, sizeof(cn)) &&
                                  strstr(cn, "Hunter")) ? 1 : 0;
            }
        } else {
            return 0;
        }
    }
 
    /* position via RootComponent->RelativeLocation */
    root = read64(actor + OFF_ACTOR_ROOT_COMPONENT);
    if (!root) return 0;
 
    rpm(root + OFF_SCENE_RELATIVE_LOCATION, &pos, sizeof(Vec3));
    if (fabs(pos.x) > 1e8 || fabs(pos.y) > 1e8 || fabs(pos.z) > 1e8)
        return 0;
 
    dx = pos.x - cam_loc.x;
    dy = pos.y - cam_loc.y;
    dz = pos.z - cam_loc.z;
    dist = sqrt(dx*dx + dy*dy + dz*dz) / 100.0;
    if (dist > 500.0) return 0;
    if (dist < 1.0) return 0; /* skip self/very close (likely local pawn) */
 
    out->pos = pos;
    out->dist = dist;
 
    /* resolve mesh component for skeleton */
    uint64_t mesh = 0;
    if (out->type == ENT_ENEMY_AI)
        mesh = read64(actor + OFF_CHAR_MESH);
    else
        mesh = read64(actor + g_off_player_mesh);
    /* validate it's a heap pointer */
    if (mesh && mesh > 0x10000ULL && mesh < 0x7FF000000000ULL)
        out->mesh_comp = mesh;
    else
        out->mesh_comp = 0;
 
    /* read player name from PlayerState */
    out->name[0] = 0;
    uint64_t ps = read64(actor + OFF_PAWN_PLAYER_STATE);
    if (ps) {
        uint64_t name_data = read64(ps + OFF_PS_PLAYER_NAME);
        int32_t name_len = read32(ps + OFF_PS_PLAYER_NAME + 8);
        if (name_data && name_len > 0 && name_len < 30) {
            uint16_t wbuf[32] = {0};
            rpm(name_data, wbuf, name_len * 2);
            for (int c = 0; c < name_len && c < 31; c++)
                out->name[c] = (char)(wbuf[c] & 0x7F);
            out->name[name_len < 31 ? name_len : 31] = 0;
        }
    }
 
    return 1;
}
 
/* ── humanized aimbot ──────────────────────────────────────── */
 
static uint32_t g_rng = 0;
 
static uint32_t xorshift32(void) {
    g_rng ^= g_rng << 13;
    g_rng ^= g_rng >> 17;
    g_rng ^= g_rng << 5;
    return g_rng;
}
 
static float randf(void) { return (float)(xorshift32() % 10001) / 10000.0f; }
static float randf_range(float lo, float hi) { return lo + randf() * (hi - lo); }
static float randf_signed(void) { return randf() * 2.0f - 1.0f; }
 
static float ease_out_quart(float t) {
    float u = 1.0f - t;
    return 1.0f - u * u * u * u;
}
 
static void aimbot_init(void) {
    g_rng = GetTickCount() ^ 0xDEADBEEF;
    memset(&g_aim_st, 0, sizeof(g_aim_st));
    g_aim_cfg.fov_radius          = 120.0f;
    g_aim_cfg.smoothing_near      = 18.0f;
    g_aim_cfg.smoothing_far       = 4.0f;
    g_aim_cfg.dead_zone           = 1.5f;
    g_aim_cfg.head_offset         = 130.0f;
    g_aim_cfg.jitter_amplitude    = 1.2f;
    g_aim_cfg.jitter_interval_ms  = 80.0f;
    g_aim_cfg.wander_radius       = 3.5f;
    g_aim_cfg.wander_interval_ms  = 500.0f;
    g_aim_cfg.overshoot_chance    = 0.25f;
    g_aim_cfg.overshoot_distance  = 12.0f;
    g_aim_cfg.overshoot_decay_ms  = 200.0f;
    g_aim_cfg.reaction_min_ms     = 120.0f;
    g_aim_cfg.reaction_max_ms     = 280.0f;
    g_aim_cfg.switch_cooldown_ms  = 400.0f;
    g_aim_cfg.sticky_score_bonus  = 0.6f;
    g_aim_cfg.sticky_fov_mult     = 1.6f;
    g_aim_cfg.distance_weight     = 0.3f;
    g_aim_cfg.crosshair_weight    = 1.0f;
    g_aim_cfg.max_move_per_frame  = 35.0f;
    g_aim_cfg.velocity_inertia    = 0.3f;
    g_aim_cfg.target_ai           = 1;
    g_aim_cfg.target_players      = 1;
}
 
static void aimbot_update_jitter(void) {
    DWORD now = GetTickCount();
    if (now >= g_aim_st.jitter_next) {
        g_aim_st.jitter_goal_x = randf_signed() * g_aim_cfg.jitter_amplitude;
        g_aim_st.jitter_goal_y = randf_signed() * g_aim_cfg.jitter_amplitude;
        g_aim_st.jitter_next = now +
            (DWORD)(g_aim_cfg.jitter_interval_ms * randf_range(0.7f, 1.3f));
    }
    g_aim_st.jitter_x += (g_aim_st.jitter_goal_x - g_aim_st.jitter_x) * 0.15f;
    g_aim_st.jitter_y += (g_aim_st.jitter_goal_y - g_aim_st.jitter_y) * 0.15f;
}
 
static void aimbot_update_wander(void) {
    DWORD now = GetTickCount();
    if (now >= g_aim_st.wander_next) {
        float angle = randf() * 2.0f * (float)PI;
        float r = randf() * g_aim_cfg.wander_radius;
        g_aim_st.wander_goal_x = cosf(angle) * r;
        g_aim_st.wander_goal_y = sinf(angle) * r;
        g_aim_st.wander_next = now +
            (DWORD)(g_aim_cfg.wander_interval_ms * randf_range(0.6f, 1.4f));
    }
    g_aim_st.wander_x += (g_aim_st.wander_goal_x - g_aim_st.wander_x) * 0.05f;
    g_aim_st.wander_y += (g_aim_st.wander_goal_y - g_aim_st.wander_y) * 0.05f;
}
 
static void aimbot_try_overshoot(float dx, float dy) {
    float dist = sqrtf(dx * dx + dy * dy);
    if (dist < 20.0f || randf() > g_aim_cfg.overshoot_chance) return;
    float scale = randf_range(0.3f, 1.0f);
    g_aim_st.overshooting = 1;
    g_aim_st.overshoot_x = (dx / dist) * g_aim_cfg.overshoot_distance * scale;
    g_aim_st.overshoot_y = (dy / dist) * g_aim_cfg.overshoot_distance * scale;
    g_aim_st.overshoot_end = GetTickCount() +
        (DWORD)(g_aim_cfg.overshoot_decay_ms * randf_range(0.8f, 1.2f));
}
 
static float aimbot_dynamic_smooth(float screen_dist) {
    float t = screen_dist / g_aim_cfg.fov_radius;
    if (t > 1.0f) t = 1.0f;
    if (t < 0.0f) t = 0.0f;
    float eased = ease_out_quart(t);
    float smooth = g_aim_cfg.smoothing_near +
        (g_aim_cfg.smoothing_far - g_aim_cfg.smoothing_near) * eased;
    smooth *= randf_range(0.85f, 1.15f);
    return smooth;
}
 
static float aimbot_score(float crosshair_dist, float world_dist, int is_locked) {
    float score = crosshair_dist * g_aim_cfg.crosshair_weight +
                  world_dist * g_aim_cfg.distance_weight;
    if (is_locked) score *= g_aim_cfg.sticky_score_bonus;
    return score;
}
 
static void aimbot_acquire(uint64_t actor, float dx, float dy) {
    DWORD now = GetTickCount();
    g_aim_st.has_target = 1;
    g_aim_st.locked_actor = actor;
    g_aim_st.lock_time = now;
    g_aim_st.last_switch = now;
    g_aim_st.miss_frames = 0;
    g_aim_st.vel_x = 0;
    g_aim_st.vel_y = 0;
    g_aim_st.in_reaction_delay = 1;
    g_aim_st.reaction_end = now +
        (DWORD)randf_range(g_aim_cfg.reaction_min_ms, g_aim_cfg.reaction_max_ms);
    aimbot_try_overshoot(dx, dy);
}
 
static void aimbot_release(void) {
    g_aim_st.has_target = 0;
    g_aim_st.locked_actor = 0;
    g_aim_st.vel_x = 0;
    g_aim_st.vel_y = 0;
    g_aim_st.overshooting = 0;
    g_aim_st.in_reaction_delay = 0;
    g_aim_st.jitter_x = 0;
    g_aim_st.jitter_y = 0;
    g_aim_st.wander_x = 0;
    g_aim_st.wander_y = 0;
}
 
static void aimbot_move(float target_sx, float target_sy) {
    float cx = g_screen_w / 2.0f;
    float cy = g_screen_h / 2.0f;
    float dx = target_sx - cx;
    float dy = target_sy - cy;
 
    if (g_aim_st.in_reaction_delay) {
        if (GetTickCount() < g_aim_st.reaction_end) return;
        g_aim_st.in_reaction_delay = 0;
    }
 
    aimbot_update_jitter();
    aimbot_update_wander();
 
    dx += g_aim_st.jitter_x + g_aim_st.wander_x;
    dy += g_aim_st.jitter_y + g_aim_st.wander_y;
 
    if (g_aim_st.overshooting) {
        DWORD now = GetTickCount();
        if (now < g_aim_st.overshoot_end) {
            float t = (float)(g_aim_st.overshoot_end - now) / g_aim_cfg.overshoot_decay_ms;
            dx += g_aim_st.overshoot_x * t;
            dy += g_aim_st.overshoot_y * t;
        } else {
            g_aim_st.overshooting = 0;
        }
    }
 
    float dist = sqrtf(dx * dx + dy * dy);
    if (dist < g_aim_cfg.dead_zone) return;
 
    float smooth = aimbot_dynamic_smooth(dist);
    float want_vx = dx / smooth;
    float want_vy = dy / smooth;
 
    float inertia = g_aim_cfg.velocity_inertia;
    float move_x = g_aim_st.vel_x * inertia + want_vx * (1.0f - inertia);
    float move_y = g_aim_st.vel_y * inertia + want_vy * (1.0f - inertia);
    g_aim_st.vel_x = move_x;
    g_aim_st.vel_y = move_y;
 
    if (fabsf(move_x) < 1.0f && fabsf(move_x) > 0.05f)
        move_x = (move_x > 0) ? 1.0f : -1.0f;
    if (fabsf(move_y) < 1.0f && fabsf(move_y) > 0.05f)
        move_y = (move_y > 0) ? 1.0f : -1.0f;
 
    float cap = g_aim_cfg.max_move_per_frame;
    if (fabsf(move_x) > cap) move_x = (move_x > 0) ? cap : -cap;
    if (fabsf(move_y) > cap) move_y = (move_y > 0) ? cap : -cap;
 
    INPUT input = {0};
    input.type = INPUT_MOUSE;
    input.mi.dx = (LONG)move_x;
    input.mi.dy = (LONG)move_y;
    input.mi.dwFlags = MOUSEEVENTF_MOVE;
    SendInput(1, &input, sizeof(INPUT));
}
 
typedef struct {
    uint64_t actor;
    float    screen_x, screen_y;
    float    crosshair_dist;
    float    world_dist;
    float    score;
    int      valid;
} AimCandidate;
 
static void draw_circle(HDC hdc, HPEN pen, int cx, int cy, int r) {
    SelectObject(hdc, pen);
    SelectObject(hdc, GetStockObject(NULL_BRUSH));
    Ellipse(hdc, cx - r, cy - r, cx + r, cy + r);
}
 
/* ── skeleton drawing ──────────────────────────────────────── */
 
static Vec3 read_bone_pos(uint64_t bone_array, int bone_idx) {
    Vec3 v = {0};
    uint64_t addr = bone_array + (uint64_t)bone_idx * FTRANSFORM_SIZE + FTRANSFORM_POS_OFF;
    rpm(addr, &v, sizeof(Vec3));
    return v;
}
 
static int g_bone_dumped = 0;
 
static int find_bone_array(uint64_t mesh_comp, uint64_t* out_data, int* out_count) {
    uint64_t d; int c;
    /* buffer 0 */
    d = read64(mesh_comp + OFF_BONE_ARRAY);
    c = read32(mesh_comp + OFF_BONE_ARRAY + 8);
    if (d && d > 0x10000ULL && d < 0x7FF000000000ULL && c >= 5 && c <= 200) {
        *out_data = d; *out_count = c; return 1;
    }
    /* buffer 1 */
    d = read64(mesh_comp + OFF_BONE_ARRAY2);
    c = read32(mesh_comp + OFF_BONE_ARRAY2 + 8);
    if (d && d > 0x10000ULL && d < 0x7FF000000000ULL && c >= 5 && c <= 200) {
        *out_data = d; *out_count = c; return 1;
    }
    /* CachedComponentSpaceTransforms */
    d = read64(mesh_comp + 0x9B8);
    c = read32(mesh_comp + 0x9B8 + 8);
    if (d && d > 0x10000ULL && d < 0x7FF000000000ULL && c >= 5 && c <= 200) {
        *out_data = d; *out_count = c; return 1;
    }
    return 0;
}
 
typedef struct { double x, y, z, w; } Quat4;
 
static Vec3 quat_rotate(Quat4 q, Vec3 v) {
    double tx = 2.0 * (q.y * v.z - q.z * v.y);
    double ty = 2.0 * (q.z * v.x - q.x * v.z);
    double tz = 2.0 * (q.x * v.y - q.y * v.x);
    Vec3 r;
    r.x = v.x + q.w * tx + (q.y * tz - q.z * ty);
    r.y = v.y + q.w * ty + (q.z * tx - q.x * tz);
    r.z = v.z + q.w * tz + (q.x * ty - q.y * tx);
    return r;
}
 
static Vec3 bone_to_world(Vec3 bone_cs, uint64_t mesh_comp) {
    Quat4 q = {0}; Vec3 t = {0}; Vec3 s = {0};
    rpm(mesh_comp + OFF_COMPONENT_TO_WORLD, &q, sizeof(Quat4));
    rpm(mesh_comp + OFF_COMPONENT_TO_WORLD + 0x20, &t, sizeof(Vec3));
    rpm(mesh_comp + OFF_COMPONENT_TO_WORLD + 0x40, &s, sizeof(Vec3));
    Vec3 scaled = { bone_cs.x * s.x, bone_cs.y * s.y, bone_cs.z * s.z };
    Vec3 rotated = quat_rotate(q, scaled);
    Vec3 w = { rotated.x + t.x, rotated.y + t.y, rotated.z + t.z };
    return w;
}
 
static Vec3 bone_to_world_cached(Vec3 bone_cs, Quat4 q, Vec3 t, Vec3 s) {
    Vec3 scaled = { bone_cs.x * s.x, bone_cs.y * s.y, bone_cs.z * s.z };
    Vec3 rotated = quat_rotate(q, scaled);
    Vec3 w = { rotated.x + t.x, rotated.y + t.y, rotated.z + t.z };
    return w;
}
 
static void draw_skeleton(HDC hdc, HPEN pen, uint64_t mesh_comp,
                          Vec3 actor_pos, Vec3 cam_loc, Rot3 cam_rot, float fov) {
    if (!mesh_comp) return;
 
    uint64_t bone_data = 0;
    int bone_count = 0;
    if (!find_bone_array(mesh_comp, &bone_data, &bone_count)) return;
 
    if (!g_bone_dumped) {
        g_bone_dumped = 1;
        Quat4 dq = {0}; Vec3 dt = {0};
        rpm(mesh_comp + OFF_COMPONENT_TO_WORLD, &dq, sizeof(Quat4));
        rpm(mesh_comp + OFF_COMPONENT_TO_WORLD + 0x20, &dt, sizeof(Vec3));
        FILE* bf = fopen("C:\\Chrome\\logs\\bone_dump.txt", "w");
        if (bf) {
            fprintf(bf, "mesh=0x%llX  bone_data=0x%llX  bone_count=%d\n",
                    (unsigned long long)mesh_comp, (unsigned long long)bone_data, bone_count);
            fprintf(bf, "CTW quat=(%.6f, %.6f, %.6f, %.6f)\n", dq.x, dq.y, dq.z, dq.w);
            fprintf(bf, "CTW pos=(%.1f, %.1f, %.1f)\n", dt.x, dt.y, dt.z);
            fprintf(bf, "actor_pos=(%.1f, %.1f, %.1f)\n", actor_pos.x, actor_pos.y, actor_pos.z);
            fprintf(bf, "\n--- raw component-space bones ---\n");
            for (int b = 0; b < bone_count && b < 40; b++) {
                Vec3 bp = read_bone_pos(bone_data, b);
                Vec3 wp = bone_to_world(bp, mesh_comp);
                fprintf(bf, "bone[%2d] cs=(%8.1f,%8.1f,%8.1f) ws=(%8.1f,%8.1f,%8.1f)\n",
                        b, bp.x, bp.y, bp.z, wp.x, wp.y, wp.z);
            }
            fprintf(bf, "\n--- trying alt offsets ---\n");
            uint64_t alts[] = {0x5F0, 0x600, 0x9B8, 0x9A8};
            for (int a = 0; a < 4; a++) {
                uint64_t ad = read64(mesh_comp + alts[a]);
                int ac = read32(mesh_comp + alts[a] + 8);
                fprintf(bf, "offset 0x%llX: data=0x%llX count=%d\n",
                        (unsigned long long)alts[a], (unsigned long long)ad, ac);
                if (ad > 0x10000ULL && ad < 0x7FF000000000ULL && ac >= 2 && ac <= 200) {
                    Vec3 b0 = read_bone_pos(ad, 0);
                    Vec3 b1 = read_bone_pos(ad, 1);
                    Vec3 b7 = read_bone_pos(ad, 7);
                    fprintf(bf, "  [0]=(%8.1f,%8.1f,%8.1f) [1]=(%8.1f,%8.1f,%8.1f) [7]=(%8.1f,%8.1f,%8.1f)\n",
                            b0.x, b0.y, b0.z, b1.x, b1.y, b1.z, b7.x, b7.y, b7.z);
                }
            }
            fclose(bf);
            printf("[+] Bone dump: C:\\Chrome\\logs\\bone_dump.txt\n");
        }
    }
 
    /* cache ComponentToWorld once per entity (not per bone) */
    Quat4 ctw_q = {0}; Vec3 ctw_t = {0}; Vec3 ctw_s = {1,1,1};
    rpm(mesh_comp + OFF_COMPONENT_TO_WORLD, &ctw_q, sizeof(Quat4));
    rpm(mesh_comp + OFF_COMPONENT_TO_WORLD + 0x20, &ctw_t, sizeof(Vec3));
    rpm(mesh_comp + OFF_COMPONENT_TO_WORLD + 0x40, &ctw_s, sizeof(Vec3));
 
    SelectObject(hdc, pen);
 
    for (int p = 0; p < (int)BONE_PAIR_COUNT; p++) {
        int from = g_bone_pairs[p].from;
        int to   = g_bone_pairs[p].to;
        if (from >= bone_count || to >= bone_count) continue;
 
        Vec3 b1 = read_bone_pos(bone_data, from);
        Vec3 b2 = read_bone_pos(bone_data, to);
 
        Vec3 w1 = bone_to_world_cached(b1, ctw_q, ctw_t, ctw_s);
        Vec3 w2 = bone_to_world_cached(b2, ctw_q, ctw_t, ctw_s);
 
        float sx1, sy1, sx2, sy2;
        if (world_to_screen(w1, cam_loc, cam_rot, fov, &sx1, &sy1) &&
            world_to_screen(w2, cam_loc, cam_rot, fov, &sx2, &sy2)) {
            MoveToEx(hdc, (int)sx1, (int)sy1, NULL);
            LineTo(hdc, (int)sx2, (int)sy2);
        }
    }
}
 
/* ── debug log ─────────────────────────────────────────────── */
 
static FILE* g_dbg = NULL;
static DWORD g_dbg_next = 0;
 
static void dbg_open(void) {
    if (g_dbg) return;
    g_dbg = fopen("C:\\Users\\Fauzinho\\Desktop\\esp_debug.txt", "w");
    if (g_dbg) setvbuf(g_dbg, NULL, _IONBF, 0);
}
 
#define DBG(fmt, ...) do { \
    printf(fmt, ##__VA_ARGS__); \
    if (g_dbg) fprintf(g_dbg, fmt, ##__VA_ARGS__); \
} while(0)
 
/* ── main ESP frame ────────────────────────────────────────── */
 
#define MAX_ACTORS 8192
 
static int g_dbg_enabled = 1; /* show debug overlay */
static char g_dbg_lines[12][128];
static int  g_dbg_line_count = 0;
 
static void dbg_set(int idx, const char* fmt, ...) {
    if (idx < 0 || idx >= 12) return;
    va_list ap; va_start(ap, fmt);
    vsnprintf(g_dbg_lines[idx], 128, fmt, ap);
    va_end(ap);
    if (idx + 1 > g_dbg_line_count) g_dbg_line_count = idx + 1;
}
 
static void draw_debug_overlay(HDC hdc) {
    if (!g_dbg_enabled) return;
    SetBkMode(hdc, TRANSPARENT);
    for (int i = 0; i < g_dbg_line_count; i++) {
        if (!g_dbg_lines[i][0]) continue;
        draw_text(hdc, 10, 30 + i * 15, RGB(0, 255, 0), g_dbg_lines[i]);
    }
}
 
static void esp_frame(HDC hdc) {
    uint64_t gworld, game_instance, lp_data, local_player;
    uint64_t player_controller, cam_mgr, pov_base, local_pawn, level;
    uint64_t actors_data;
    int32_t  actors_count;
    Vec3     cam_loc;
    Rot3     cam_rot;
    float    cam_fov;
    int      enemy_count = 0, player_count = 0;
    char     buf[128];
    AimCandidate best_cand = {0}; best_cand.score = 1e9f;
    AimCandidate locked_cand = {0};
    int found_locked = 0;
 
    int do_log = (GetTickCount() >= g_dbg_next);
    if (do_log) { g_dbg_next = GetTickCount() + 3000; dbg_open(); }
 
    if (!g_base) { dbg_set(0, "base=NULL"); return; }
 
    gworld = read64(g_base + g_off_gworld);
    dbg_set(0, "GWorld=0x%llX (off=0x%llX)",
        (unsigned long long)gworld, (unsigned long long)g_off_gworld);
    if (!gworld) { if (do_log) DBG("[-] GWorld NULL\n"); return; }
 
    game_instance = read64(gworld + OFF_UWORLD_GAME_INSTANCE);
    dbg_set(1, "GameInstance=0x%llX", (unsigned long long)game_instance);
    if (!game_instance) { if (do_log) DBG("[-] GameInstance NULL\n"); return; }
 
    lp_data = read64(game_instance + OFF_GI_LOCAL_PLAYERS);
    local_player = lp_data ? read64(lp_data) : 0;
    dbg_set(2, "LocalPlayer=0x%llX (data=0x%llX)",
        (unsigned long long)local_player, (unsigned long long)lp_data);
    if (!local_player) { if (do_log) DBG("[-] LocalPlayer NULL\n"); return; }
 
    player_controller = read64(local_player + OFF_PLAYER_CONTROLLER);
    dbg_set(3, "PC=0x%llX", (unsigned long long)player_controller);
    if (!player_controller) { if (do_log) DBG("[-] PlayerController NULL\n"); return; }
 
    cam_mgr = read64(player_controller + OFF_PC_CAMERA_MANAGER);
    dbg_set(4, "CamMgr=0x%llX", (unsigned long long)cam_mgr);
    if (!cam_mgr) { if (do_log) DBG("[-] CamMgr NULL\n"); return; }
 
    pov_base = cam_mgr + OFF_CAM_CACHE + OFF_CACHE_POV;
    rpm(pov_base + OFF_POV_LOCATION, &cam_loc, sizeof(Vec3));
    rpm(pov_base + OFF_POV_ROTATION, &cam_rot, sizeof(Rot3));
    cam_fov = readf(pov_base + OFF_POV_FOV);
    if (cam_fov < 1.0f || cam_fov > 170.0f) cam_fov = 90.0f;
    dbg_set(5, "Pos=(%.0f,%.0f,%.0f) FOV=%.1f",
        cam_loc.x, cam_loc.y, cam_loc.z, cam_fov);
    if (do_log) DBG("[+] Pos=(%.0f,%.0f,%.0f) Rot=(%.1f,%.1f) FOV=%.1f\n",
        cam_loc.x, cam_loc.y, cam_loc.z, cam_rot.pitch, cam_rot.yaw, cam_fov);
 
    local_pawn = read64(player_controller + OFF_CONTROLLER_PAWN);
    dbg_set(6, "Pawn=0x%llX", (unsigned long long)local_pawn);
    if (do_log) DBG("[+] Pawn=0x%llX\n", (unsigned long long)local_pawn);
 
    uint8_t local_is_hunter = 0;
    if (local_pawn && g_fname_pool) {
        uint64_t lc = read64(local_pawn + UOBJECT_CLASS);
        uint32_t lf = lc ? read32(lc + 0x18) : 0;
        char ln[128];
        local_is_hunter = (fname_to_string(lf, ln, sizeof(ln)) && strstr(ln, "Hunter")) ? 1 : 0;
    }
 
    /* iterate ALL levels (persistent + streaming sublevels) */
    uint64_t all_levels_ptr   = read64(gworld + 0x01C8);
    int32_t  all_levels_count = read32(gworld + 0x01C8 + 8);
    if (all_levels_count < 0 || all_levels_count > 512) all_levels_count = 0;
    dbg_set(7, "Levels ptr=0x%llX cnt=%d", (unsigned long long)all_levels_ptr, all_levels_count);
    if (do_log) DBG("[+] Levels ptr=0x%llX count=%d\n",
        (unsigned long long)all_levels_ptr, all_levels_count);
 
    static uint64_t actor_ptrs[MAX_ACTORS];
    int read_count = 0;
    int total_levels_actors = 0;
 
    for (int li = 0; li < all_levels_count; li++) {
        uint64_t lv = read64(all_levels_ptr + (uint64_t)li * 8);
        if (!lv) continue;
        uint64_t lv_actors_data  = read64(lv + OFF_ULEVEL_ACTORS);
        int32_t  lv_actors_count = read32(lv + OFF_ULEVEL_ACTORS + 8);
        if (lv_actors_count <= 0 || lv_actors_count > 50000) continue;
        total_levels_actors += lv_actors_count;
        int can_read = MAX_ACTORS - read_count;
        if (can_read <= 0) break;
        if (lv_actors_count < can_read) can_read = lv_actors_count;
        rpm(lv_actors_data, actor_ptrs + read_count, (size_t)can_read * 8);
        read_count += can_read;
    }
    /* inject PlayerArray pawns directly — guaranteed player actors, no false positives */
    uint64_t gs_inject = read64(gworld + 0x1B0);
    int pa_injected = 0;
    if (gs_inject) {
        uint64_t pa_data2  = read64(gs_inject + 0x2C0);
        int32_t  pa_cnt2   = read32(gs_inject + 0x2C0 + 8);
        if (pa_cnt2 > 0 && pa_cnt2 < 512 && pa_data2) {
            for (int pi = 0; pi < pa_cnt2; pi++) {
                uint64_t ps  = read64(pa_data2 + (uint64_t)pi * 8);
                if (!ps) continue;
                uint64_t pawn = read64(ps + 0x320); /* PawnPrivate */
                if (!pawn) continue;
                /* dedup: skip if already from level scan */
                int dup = 0;
                for (int k = 0; k < read_count; k++) {
                    if (actor_ptrs[k] == pawn) { dup = 1; break; }
                }
                if (!dup && read_count < MAX_ACTORS) {
                    actor_ptrs[read_count++] = pawn;
                    pa_injected++;
                }
            }
        }
    }
    dbg_set(8, "Actors total=%d read=%d pa+%d", total_levels_actors, read_count - pa_injected, pa_injected);
    if (do_log) DBG("[+] AllActors total=%d read=%d pa_injected=%d\n", total_levels_actors, read_count - pa_injected, pa_injected);
    if (read_count == 0) return;
 
    /* dump first 10 actors to log every 3 sec */
    /* show first 3 actors on screen always + dump to log every 3s */
    {
        char abuf[128];
        for (int di = 0; di < 3 && di < read_count; di++) {
            uint64_t a = actor_ptrs[di];
            double ph = a ? readd(a + 0x640) : 0;
            double pm = a ? readd(a + 0x648) : 0;
            snprintf(abuf, sizeof(abuf), "a[%d]=0x%llX pH=%.1f/%.1f",
                di, (unsigned long long)a, ph, pm);
            dbg_set(10 + di, abuf);
        }
        /* GameState -> PlayerArray */
        uint64_t gs = read64(gworld + 0x1B0);
        uint64_t pa_data = gs ? read64(gs + 0x2C0) : 0;
        int32_t  pa_cnt  = gs ? read32(gs + 0x2C0 + 8) : 0;
        dbg_set(9, "GS=0x%llX PA cnt=%d", (unsigned long long)gs, pa_cnt);
    }
    if (do_log) {
        dbg_open();
        DBG("--- actor dump (first 10 of %d) ---\n", read_count);
        for (int di = 0; di < read_count && di < 10; di++) {
            uint64_t a = actor_ptrs[di];
            uint64_t vt = a ? read64(a) : 0;
            double eh = a ? readd(a + 0x8D8) : 0;
            double em = a ? readd(a + 0x908) : 0;
            double ph = a ? readd(a + 0x640) : 0;
            double pm = a ? readd(a + 0x648) : 0;
            DBG("  [%d] a=0x%llX vt=0x%llX eH=%.2f/%.2f pH=%.2f/%.2f\n",
                di, (unsigned long long)a, (unsigned long long)vt,
                eh, em, ph, pm);
        }
        uint64_t gs2 = read64(gworld + 0x1B0);
        uint64_t pa2 = gs2 ? read64(gs2 + 0x2C0) : 0;
        int32_t  pc2 = gs2 ? read32(gs2 + 0x2C0 + 8) : 0;
        DBG("  GS=0x%llX PA ptr=0x%llX cnt=%d\n",
            (unsigned long long)gs2, (unsigned long long)pa2, pc2);
    }
 
    HFONT old_font = (HFONT)SelectObject(hdc, g_font);
 
    for (int i = 0; i < read_count; i++) {
        EntInfo ent = {0};
        if (!try_read_entity(actor_ptrs[i], local_pawn, cam_loc, &ent))
            continue;
 
        if (ent.type == ENT_ENEMY_AI && !g_menu.show_ai) continue;
        if (ent.type == ENT_PLAYER   && !g_menu.show_players) continue;
        /* team filter: same hunter status = same team */
        if (ent.type == ENT_PLAYER && g_menu.enemy_only &&
            ent.is_hunter == local_is_hunter) continue;
 
        float sx, sy, hx, hy, fx, fy;
 
        /* use mesh ComponentToWorld position if we have a mesh, else actor pos */
        Vec3 base_pos = ent.pos;
        if (ent.mesh_comp) {
            Vec3 ctw_pos = {0};
            rpm(ent.mesh_comp + OFF_COMPONENT_TO_WORLD + 0x20, &ctw_pos, sizeof(Vec3));
            if (fabs(ctw_pos.x) > 0.1 || fabs(ctw_pos.y) > 0.1)
                base_pos = ctw_pos;
        }
        /* compute screen-space bounding box from bones if available */
        float bx, by, box_w, box_h;
        uint64_t bb_data = 0; int bb_count = 0;
        int has_bone_box = 0;
 
        if (ent.mesh_comp && find_bone_array(ent.mesh_comp, &bb_data, &bb_count) && bb_count >= 5) {
            Quat4 bq = {0}; Vec3 bt = {0}; Vec3 bs = {1,1,1};
            rpm(ent.mesh_comp + OFF_COMPONENT_TO_WORLD, &bq, sizeof(Quat4));
            rpm(ent.mesh_comp + OFF_COMPONENT_TO_WORLD + 0x20, &bt, sizeof(Vec3));
            rpm(ent.mesh_comp + OFF_COMPONENT_TO_WORLD + 0x40, &bs, sizeof(Vec3));
 
            float min_sx = 99999, min_sy = 99999, max_sx = -99999, max_sy = -99999;
            int visible_bones = 0;
            for (int b = 0; b < bb_count; b++) {
                Vec3 bp = read_bone_pos(bb_data, b);
                Vec3 wp = bone_to_world_cached(bp, bq, bt, bs);
                float bsx, bsy;
                if (world_to_screen(wp, cam_loc, cam_rot, cam_fov, &bsx, &bsy)) {
                    if (bsx < min_sx) min_sx = bsx;
                    if (bsy < min_sy) min_sy = bsy;
                    if (bsx > max_sx) max_sx = bsx;
                    if (bsy > max_sy) max_sy = bsy;
                    visible_bones++;
                }
            }
            if (visible_bones >= 3) {
                float pad = 8.0f;
                bx = min_sx - pad;
                by = min_sy - pad;
                box_w = (max_sx - min_sx) + pad * 2;
                box_h = (max_sy - min_sy) + pad * 2;
                sx = (min_sx + max_sx) / 2.0f;
                sy = max_sy;
                fx = sx; fy = sy; hx = sx; hy = min_sy;
                has_bone_box = 1;
            }
        }
 
        if (!has_bone_box) {
            Vec3 head = base_pos; head.z += 130.0;
            Vec3 feet = base_pos;
            if (!world_to_screen(feet, cam_loc, cam_rot, cam_fov, &fx, &fy)) continue;
            if (!world_to_screen(head, cam_loc, cam_rot, cam_fov, &hx, &hy)) continue;
            sx = (fx + hx) / 2.0f;
            sy = fy;
            box_h = fy - hy;
            if (box_h < 15) box_h = 30;
            box_w = box_h * 0.6f;
            bx = fx - box_w / 2;
            by = hy;
        }
 
        HPEN box_pen;
        COLORREF text_col;
 
        if (ent.type == ENT_ENEMY_AI) {
            box_pen   = ent.is_down ? g_yellow_pen : g_red_pen;
            text_col  = ent.is_down ? RGB(255,255,0) : RGB(255,80,80);
            enemy_count++;
        } else {
            box_pen   = (ent.hp <= 0) ? g_yellow_pen : g_cyan_pen;
            text_col  = (ent.hp <= 0) ? RGB(255,255,0) : RGB(0,255,255);
            player_count++;
        }
 
        /* corner box */
        if (g_menu.show_boxes)
            draw_corner_box(hdc, box_pen, (int)bx, (int)by, (int)box_w, (int)box_h);
 
        /* skeleton */
        if (g_menu.show_boxes && ent.mesh_comp) {
            HPEN skel_pen = (ent.type == ENT_ENEMY_AI) ? g_red_pen : g_cyan_pen;
            draw_skeleton(hdc, skel_pen, ent.mesh_comp,
                          ent.pos, cam_loc, cam_rot, cam_fov);
        }
 
        /* health bar */
        if (g_menu.show_health)
            draw_health_bar(hdc, (int)(bx + box_w + 4), (int)by, 4, (int)box_h,
                            ent.hp, ent.max_hp);
 
        /* name + info label */
        if (g_menu.show_labels) {
            if (ent.name[0])
                draw_text_shadow(hdc, (int)bx, (int)(by - 30), RGB(220,220,230), ent.name);
            snprintf(buf, sizeof(buf), "%.0fm HP:%.0f/%.0f%s",
                     ent.dist, ent.hp, ent.max_hp,
                     ent.is_down ? " DOWN" : "");
            draw_text_shadow(hdc, (int)bx, (int)(by - 16), text_col, buf);
        }
 
        /* aimbot candidate registration */
        if (g_menu.aim_enabled && ent.hp > 0 && !ent.is_down) {
            int want = (ent.type == ENT_ENEMY_AI && g_aim_cfg.target_ai) ||
                       (ent.type == ENT_PLAYER   && g_aim_cfg.target_players);
            if (want) {
                Vec3 aim_pt;
                /* use actual head bone position if mesh has bone data */
                uint64_t ab_data = 0; int ab_count = 0;
                if (ent.mesh_comp && find_bone_array(ent.mesh_comp, &ab_data, &ab_count) && BONE_HEAD < ab_count) {
                    Vec3 head_bone = read_bone_pos(ab_data, BONE_HEAD);
                    aim_pt = bone_to_world(head_bone, ent.mesh_comp);
                } else {
                    aim_pt = base_pos;
                    aim_pt.z += g_aim_cfg.head_offset;
                }
                float ax, ay;
                if (world_to_screen(aim_pt, cam_loc, cam_rot, cam_fov, &ax, &ay)) {
                    float adx = ax - g_screen_w / 2.0f;
                    float ady = ay - g_screen_h / 2.0f;
                    float ad = sqrtf(adx*adx + ady*ady);
                    int is_locked = (actor_ptrs[i] == g_aim_st.locked_actor);
                    float effective_fov = g_aim_cfg.fov_radius;
                    if (is_locked) effective_fov *= g_aim_cfg.sticky_fov_mult;
                    if (ad < effective_fov) {
                        float score = aimbot_score(ad, (float)ent.dist, is_locked);
                        if (is_locked) {
                            found_locked = 1;
                            locked_cand.actor = actor_ptrs[i];
                            locked_cand.screen_x = ax;
                            locked_cand.screen_y = ay;
                            locked_cand.crosshair_dist = ad;
                            locked_cand.world_dist = (float)ent.dist;
                            locked_cand.score = score;
                            locked_cand.valid = 1;
                        }
                        if (score < best_cand.score) {
                            best_cand.actor = actor_ptrs[i];
                            best_cand.screen_x = ax;
                            best_cand.screen_y = ay;
                            best_cand.crosshair_dist = ad;
                            best_cand.world_dist = (float)ent.dist;
                            best_cand.score = score;
                            best_cand.valid = 1;
                        }
                    }
                }
            }
        }
    }
 
    /* aimbot FOV circle */
    if (g_menu.aim_enabled) {
        if (g_menu.show_fov_circle)
            draw_circle(hdc, g_fov_pen, g_screen_w/2, g_screen_h/2, (int)g_aim_cfg.fov_radius);
    }
 
    /* aimbot target selection + execution */
    if (g_menu.aim_enabled) {
        int holding = (GetAsyncKeyState(g_aim_key) & 0x8000);
 
        if (!holding) {
            if (g_aim_st.has_target) aimbot_release();
        } else {
            if (g_aim_st.has_target) {
                if (found_locked) {
                    g_aim_st.miss_frames = 0;
                    aimbot_move(locked_cand.screen_x, locked_cand.screen_y);
                } else {
                    g_aim_st.miss_frames++;
                    if (g_aim_st.miss_frames > 10) {
                        aimbot_release();
                        if (best_cand.valid) {
                            float adx = best_cand.screen_x - g_screen_w / 2.0f;
                            float ady = best_cand.screen_y - g_screen_h / 2.0f;
                            aimbot_acquire(best_cand.actor, adx, ady);
                        }
                    }
                }
            } else if (best_cand.valid) {
                float adx = best_cand.screen_x - g_screen_w / 2.0f;
                float ady = best_cand.screen_y - g_screen_h / 2.0f;
                aimbot_acquire(best_cand.actor, adx, ady);
            }
        }
    }
 
    dbg_set(9,  "enemies=%d players=%d", enemy_count, player_count);
    if (do_log) DBG("[+] Frame: enemies=%d players=%d\n", enemy_count, player_count);
 
    /* HUD */
    snprintf(buf, sizeof(buf), "deadstar.club | %d targets | FOV %.0f",
             enemy_count + player_count, cam_fov);
    draw_text_shadow(hdc, 10, 10, RGB(160, 130, 220), buf);
 
    /* debug overlay */
    draw_debug_overlay(hdc);
 
    SelectObject(hdc, old_font);
}
 
/* ── get local pawn helper ────────────────────────────────── */

static uint64_t get_local_pawn(void) {
    if (!g_base) return 0;
    uint64_t gworld = read64(g_base + g_off_gworld);
    if (!gworld) return 0;
    uint64_t gi = read64(gworld + OFF_UWORLD_GAME_INSTANCE);
    uint64_t lp = gi ? read64(read64(gi + OFF_GI_LOCAL_PLAYERS)) : 0;
    uint64_t pc = lp ? read64(lp + OFF_PLAYER_CONTROLLER) : 0;
    return pc ? read64(pc + OFF_CONTROLLER_PAWN) : 0;
}

/* ── infinite ammo ─────────────────────────────────────────── */

static void ammo_infinite(void) {
    if (!g_menu.ammo_infinite || !g_base) return;
    uint64_t pawn = get_local_pawn();
    if (!pawn || !g_off_ammo_current) return;

    /* try writing to weapon first, then pawn as fallback */
    uint64_t target = pawn;
    if (g_off_current_weapon) {
        uint64_t weapon = read64(pawn + g_off_current_weapon);
        if (weapon) target = weapon;
    }

    /* try double ammo write (UE5 LWC) */
    double val = 999.0;
    if (g_off_ammo_max) {
        double max_val = readd(target + g_off_ammo_max);
        if (max_val > 0 && max_val < 99999) val = max_val;
    }
    writed(target + g_off_ammo_current, val);

    /* also try float ammo write (4 bytes) */
    float fval = (float)val;
    wpm(target + g_off_ammo_current, &fval, 4);

    /* try int32 ammo write */
    int32_t ival = (int32_t)val;
    wpm(target + g_off_ammo_current, &ival, 4);
}

/* ── invisible ────────────────────────────────────────────── */

static void invisible_update(void) {
    if (!g_menu.invisible || !g_base) return;
    uint64_t pawn = get_local_pawn();
    if (!pawn) return;
    uint8_t off = 0, on = 1;
    wpm(pawn + 0xC50, &off, 1);  /* BodyVisibility = 0 */
    wpm(pawn + 0xC51, &off, 1);  /* LocalFound = 0 */
    /* also hide nameplate */
    wpm(pawn + 0xC61, &off, 1);  /* CurrentNamePlateVisibility = 0 */
}

/* ── noclip ───────────────────────────────────────────────── */

static void noclip_update(void) {
    if (!g_menu.noclip || !g_base) return;
    uint64_t pawn = get_local_pawn();
    if (!pawn) return;
    /* disable collision */
    uint8_t byte_at_5d = 0;
    rpm(pawn + 0x5D, &byte_at_5d, 1);
    byte_at_5d &= ~1;  /* clear bit 0 = bActorEnableCollision */
    wpm(pawn + 0x5D, &byte_at_5d, 1);
}

/* ── speed boost ──────────────────────────────────────────── */

static void speed_update(void) {
    if (!g_menu.speed_boost || !g_base) return;
    uint64_t pawn = get_local_pawn();
    if (!pawn) return;
    double speed = (double)g_speed_value;
    wpm(pawn + 0x5B0, &speed, 8);     /* DefaultSpeed */
    wpm(pawn + 0x0A50, &speed, 8);    /* BoostSpeed */
}

/* ── god mode ─────────────────────────────────────────────── */

static void god_mode_update(void) {
    if (!g_menu.god_mode || !g_base) return;
    uint64_t pawn = get_local_pawn();
    if (!pawn) return;
    uint8_t inv = 1;
    wpm(pawn + 0x5AB, &inv, 1);
}

/* ── rage mode (kill all enemies) ─────────────────────────── */

static void rage_update(void) {
    if (!g_menu.rage_mode || !g_base || !g_off_enemy_health) return;
    uint64_t gworld = read64(g_base + g_off_gworld);
    if (!gworld) return;
    uint64_t pawn = get_local_pawn();

    Vec3 cam_loc = {0}; Rot3 cam_rot = {0}; float cam_fov = 90;
    uint64_t gi2 = read64(gworld + OFF_UWORLD_GAME_INSTANCE);
    uint64_t lp2 = gi2 ? read64(read64(gi2 + OFF_GI_LOCAL_PLAYERS)) : 0;
    uint64_t pc2 = lp2 ? read64(lp2 + OFF_PLAYER_CONTROLLER) : 0;
    uint64_t cam_mgr = pc2 ? read64(pc2 + OFF_PC_CAMERA_MANAGER) : 0;
    if (cam_mgr) {
        uint64_t pov = cam_mgr + OFF_CAM_CACHE + OFF_CACHE_POV;
        rpm(pov + OFF_POV_LOCATION, &cam_loc, sizeof(Vec3));
        rpm(pov + OFF_POV_ROTATION, &cam_rot, sizeof(Rot3));
        cam_fov = readf(pov + OFF_POV_FOV);
    }

    uint64_t level = gworld ? read64(gworld + 0x30) : 0;
    uint64_t actors_data = level ? read64(level + OFF_ULEVEL_ACTORS) : 0;
    int32_t actors_count = level ? read32(level + OFF_ULEVEL_ACTORS + 8) : 0;
    if (!actors_data || actors_count <= 0) return;

    for (int i = 0; i < actors_count && i < 5000; i++) {
        uint64_t actor = read64(actors_data + i * 8);
        if (!actor || actor == pawn) continue;
        double hp = readd(actor + g_off_enemy_health);
        double max_hp = readd(actor + g_off_enemy_max_health);
        if (max_hp >= 1.0 && max_hp <= 50000.0 && hp > 0 && hp <= max_hp + 1.0) {
            double zero = 0.0;
            wpm(actor + g_off_enemy_health, &zero, 8);
        }
    }
}

/* ── main ──────────────────────────────────────────────────── */

int main(void) {
    printf("[*] deadstar.club - external overlay\n");
 
    g_pid = find_pid("PenguinHotel-Win64-Shipping.exe");
    if (!g_pid) { printf("[-] Game not running\n"); return 1; }
    printf("[+] PID: %u\n", g_pid);
 
    g_proc = OpenProcess(PROCESS_VM_READ | PROCESS_VM_WRITE | PROCESS_VM_OPERATION |
                         PROCESS_QUERY_INFORMATION, FALSE, g_pid);
    if (!g_proc) { printf("[-] OpenProcess failed (%lu)\n", GetLastError()); return 1; }
    printf("[+] Process opened\n");
 
    /* get module base */
    {
        HANDLE snap = CreateToolhelp32Snapshot(TH32CS_SNAPMODULE, g_pid);
        if (snap != INVALID_HANDLE_VALUE) {
            MODULEENTRY32 me = { .dwSize = sizeof(me) };
            if (Module32First(snap, &me))
                g_base = (uint64_t)me.modBaseAddr;
            CloseHandle(snap);
        }
        if (!g_base) { printf("[-] Failed to get module base\n"); return 1; }
        printf("[+] Base: 0x%llX\n", (unsigned long long)g_base);
    }
 
    /* sig scan for dynamic offsets */
    resolve_offsets();
    fflush(stdout);
 
    g_game_wnd = find_game_window();
    if (g_game_wnd) {
        RECT rc; GetClientRect(g_game_wnd, &rc);
        g_screen_w = rc.right; g_screen_h = rc.bottom;
        printf("[+] Window: %dx%d\n", g_screen_w, g_screen_h);
    } else {
        g_screen_w = GetSystemMetrics(SM_CXSCREEN);
        g_screen_h = GetSystemMetrics(SM_CYSCREEN);
    }
 
    WNDCLASSA wc = { .lpfnWndProc = overlay_proc,
                     .hInstance = GetModuleHandleA(NULL),
                     .lpszClassName = "deadstar.club" };
    RegisterClassA(&wc);
 
    g_overlay = CreateWindowExA(
        WS_EX_TOPMOST | WS_EX_TRANSPARENT | WS_EX_LAYERED | WS_EX_TOOLWINDOW,
        wc.lpszClassName, "deadstar.club", WS_POPUP,
        0, 0, g_screen_w, g_screen_h,
        NULL, NULL, wc.hInstance, NULL);
 
    SetLayeredWindowAttributes(g_overlay, RGB(0,0,0), 0, LWA_COLORKEY);
    MARGINS margins = {-1,-1,-1,-1};
    DwmExtendFrameIntoClientArea(g_overlay, &margins);
    ShowWindow(g_overlay, SW_SHOW);
 
    create_gdi_resources();
    aimbot_init();
    init_menu_items();
 
    printf("[+] Overlay active -- END to exit\n");
    fflush(stdout);
 
    int frame = 0;
    MSG msg;
    while (1) {
        while (PeekMessageA(&msg, NULL, 0, 0, PM_REMOVE)) {
            if (msg.message == WM_QUIT) goto done;
            TranslateMessage(&msg); DispatchMessageA(&msg);
        }
        if (GetAsyncKeyState(VK_END) & 0x8000) break;
        handle_hotkeys();
 
        /* hide overlay when game not focused */
        int game_fg = is_game_foreground();
        set_overlay_visible(game_fg);
        if (!game_fg) { Sleep(50); continue; }
 
        /* check game alive every 60 frames (~1sec) */
        if (++frame % 60 == 0) {
            DWORD exit_code = 0;
            if (!GetExitCodeProcess(g_proc, &exit_code) || exit_code != STILL_ACTIVE) {
                printf("[!] Game closed\n"); break;
            }
            sync_overlay_to_game();
        }
 
        HDC hdc = GetDC(g_overlay);
        HDC mem = CreateCompatibleDC(hdc);
        HBITMAP bmp = CreateCompatibleBitmap(hdc, g_screen_w, g_screen_h);
        HBITMAP old_bmp = (HBITMAP)SelectObject(mem, bmp);
 
        HBRUSH clr = CreateSolidBrush(RGB(0,0,0));
        RECT rc = {0, 0, g_screen_w, g_screen_h};
        FillRect(mem, &rc, clr);
        DeleteObject(clr);
 
        if (g_menu.esp_enabled)
            esp_frame(mem);
        ammo_infinite();
        god_mode_update();
        invisible_update();
        noclip_update();
        speed_update();
        rage_update();
        draw_menu(mem);
 
        BitBlt(hdc, 0, 0, g_screen_w, g_screen_h, mem, 0, 0, SRCCOPY);
        SelectObject(mem, old_bmp);
        DeleteObject(bmp);
        DeleteDC(mem);
        ReleaseDC(g_overlay, hdc);
 
        Sleep(16);
    }
 
done:
    destroy_gdi_resources();
    DestroyWindow(g_overlay);
    if (g_proc) CloseHandle(g_proc);
    printf("[*] Done\n");
    return 0;
}