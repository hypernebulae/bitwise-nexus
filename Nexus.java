package bitwise;

import java.awt.*;
import java.awt.datatransfer.*;
import java.awt.event.*;
import java.awt.image.*;
import java.io.*;
import java.math.BigDecimal;
import java.nio.file.*;
import java.text.*;
import java.util.*;
import java.util.List;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;
import java.util.concurrent.locks.LockSupport;
import java.util.zip.*;

import javax.sound.sampled.*;
import javax.imageio.ImageIO;
import javax.swing.*;
import javax.swing.filechooser.FileNameExtensionFilter;

import static bitwise.Nexus.*;

@SuppressWarnings("serial")
public class Nexus extends JPanel implements KeyListener, MouseListener, MouseMotionListener, FocusListener, MouseWheelListener {
	/** Player / previous-tick / interpolated-view position: 63-bit integer part + double fraction. */
	static final SplitDecimal x = new SplitDecimal(), y = new SplitDecimal(), z = new SplitDecimal();
	static final SplitDecimal prevX = new SplitDecimal(), prevY = new SplitDecimal(), prevZ = new SplitDecimal();
	static final SplitDecimal viewX = new SplitDecimal(), viewY = new SplitDecimal(), viewZ = new SplitDecimal();
	static final SplitDecimal TMP = new SplitDecimal(); // scratch, main thread only
	static final SplitDecimal worldSpawnX = new SplitDecimal(), worldSpawnY = new SplitDecimal(), worldSpawnZ = new SplitDecimal();
	static volatile SplitDecimal[] hudPos = { new SplitDecimal(), new SplitDecimal(), new SplitDecimal() }; // EDT-safe snapshot
	static double velX, velY, velZ, yaw = 1.2, pitch, fov = 90, focal = 160, sinYaw, sinPitch, cosYaw, cosPitch, amp = 1, flight = 0.1, sensitivity = Math.PI / 1800;
	volatile static boolean vSync = true, caves = true, terrain3D = true, degrees, lock, focus, inside, update = true, sprint, fly, fill, display = true, classic = true, xor, sprintRequest, showFPS = true, showXYZ = true, showRot = true, showCyan = true, showMagenta = true, showExtra = true, freezeTime = false;
	static volatile boolean mouseLookArmed = false;
	static volatile int mouseButtonsDown = 0;
	static volatile boolean worldLoading = false;
	static long worldLoadReadyAt = 0L;
	public static byte scale = 1, detail = 1, option, heldBlock, reach = 5, power = 5;
	final static int SIZE = 64, SHIFT = 6, MASK = 63, VOL = SIZE * SIZE * SIZE;
	public static short dist = 368, radius = 6;
	static int width = 1280, height = 960, resX = 1, resY = 1;
	final static int THREADS = Math.max(1, Runtime.getRuntime().availableProcessors());
	final static int RENDER_THREADS = Math.max(1, Math.min(8, THREADS - 2));
	final static int GEN_THREADS = Math.max(1, Math.min(2, THREADS - RENDER_THREADS - 1));
	static final long NO_POS = Long.MIN_VALUE;
	volatile static long focusTime, hoveredX = NO_POS, hoveredY = NO_POS, hoveredZ = NO_POS, newHoverX = NO_POS, newHoverY = NO_POS, newHoverZ = NO_POS;
	volatile static int dirX, dirY, dirZ, newDirX, newDirY, newDirZ;
	static long activity = System.currentTimeMillis(), time, fps, frames, x0 = NO_POS, y0 = NO_POS, z0 = NO_POS, x1 = NO_POS, y1 = NO_POS, z1 = NO_POS, fpsTime = System.currentTimeMillis();
	final static byte BLOCK_COUNT = 47, AXIS_X = 0, AXIS_Y = 1, AXIS_Z = 2, CROSS = 32, perlinRes = 127;
	final static int MAGIC = 0x4E585338; // "NXS8"
	static final double[] PERLIN = new double[perlinRes + 1];
	static volatile byte[] hotbar = new byte[]{};
	public static String VERSION = "2.5";
	volatile static String hoveredType;
	static Vec3 light = new Vec3(0), sunColor = new Vec3(0), ambColor = new Vec3(0), skyColor = new Vec3(0);
	static final Vec3 SUN_LOW = new Vec3(1, 0.5, 0), SUN_DAY = new Vec3(1), SUN_NIGHT = new Vec3(0.3, 0.3, 0.5);
	static final Vec3 AMB_LOW = new Vec3(0.6, 0.5, 0.5), AMB_DAY = new Vec3(0.5), AMB_NIGHT = new Vec3(0.3, 0.3, 0.5);
	static final Vec3 SKY_LOW = Vec3.rgb(0x463C53), SKY_DAY = Vec3.rgb(0x51BAF7), SKY_NIGHT = new Vec3(0);
	static JFrame frame;
	static boolean fullscreen;
	static volatile boolean paused = false, dialogOpen = false, modifyUi = false;
	static String[] modifyValues = new String[6];
	static int modifyFocus = 0, modifyCaret = 0, modifyAnchor = 0;
	static volatile boolean settingsMenu = false, quitConfirm = false;
	// Front-end screens: 0 main, 1 worlds, 2 create world, 3 general settings.
	static volatile boolean mainMenu = true;
	static volatile int frontScreen = 0, worldSelection = 0, worldScroll = 0;
	static volatile int lastFrontClickIndex = -1;
	static volatile long lastFrontClickTime = 0;
	static volatile String createWorldName = "";
	static volatile int createNameCaret = 0, createNameAnchor = 0;
	static volatile String ampEdit = "1";
	static volatile int ampCaret = 1, ampAnchor = 1;
	static volatile boolean ampEditFocused = false;
	static volatile String frontMessage = "";
	static volatile long lastMenuFrameNs = 0;
	static final String SHARED_WORLDS_DIR = "worlds";
	static volatile int settingsPage = 0; // 0 = General, 1 = Player / Render, 2 = World
	static volatile boolean hideEverything = false, guiEnabled = false, controlsUIEnabled = false;
	static volatile double pendingAmplitude = 1;
	static volatile boolean musicEnabled = true;
	static volatile double soundVolume = 1.0, musicVolume = 0.8;
	static volatile boolean menuSliderDragging = false;
	static volatile int menuSliderTarget = -1; // 0 flight, 1 render distance, 2 sensitivity, 3 sound volume, 4 music volume
	static volatile String rgbEdit = "";
	static volatile int rgbEditChannel = -1;
	static int uiHoverX, uiHoverY, windowedWidth = width, windowedHeight = height;
	static Point windowedLocation;
	static final BitSet input = new BitSet();
	static final long[] cool = new long[1024];
	static final Queue<Runnable> tasks = new ConcurrentLinkedQueue<>();
	static Cursor hidden;
	static Robot robot;
	final static BufferedImage crosshair = new BufferedImage(CROSS, CROSS, 2);
	static volatile BufferedImage screen = new BufferedImage(1, 1, 1);
	static BufferedImage backImg = new BufferedImage(1, 1, 1);
	static int[] buffer = dataOf(backImg);
	static BufferedImage atlasImg = new BufferedImage(16, BLOCK_COUNT * 48, 2);
	static int[] atlas = ((DataBufferInt) atlasImg.getRaster().getDataBuffer()).getData();
	static final long TICK_NS = 10_000_000L;
	static final double TELEPORT = 1.0;
	static double renderAlpha;
	static World world = new World(radius);
	static final List<Render> workers = new ArrayList<>();
	static long lcx = Long.MIN_VALUE, lcy, lcz;
	static volatile boolean chunkDirty = true, needGround = true;
	static final DecimalFormat FMT3 = new DecimalFormat("0.###"), FMT1 = new DecimalFormat("0.#\u00B0");
	static Font guiFont;
	static int guiFontScale = -1;
	/** Unloaded chunks the player never edited are kept here and evicted oldest-first. 0 = no limit on that axis. */
	static int CACHE_MAX_CHUNKS = 4096;
	static long CACHE_MAX_BYTES = 64L << 20;
	/** A teleport longer than this many render radii drops and reloads every chunk. 0 = reload on every teleport. */
	static double TELEPORT_RELOAD_RADII = 1.0;
	/** Shadow sub-cells per block (16 = one per texel). 0 = exact per-pixel shadow rays, no cache. */
	static int SHADOW_GRID = 8;
	/** Sun direction used for shadow rays is refreshed this often (ticks, 100/s). 0 = every frame (exact, but no cross-frame reuse). */
	static int SHADOW_REFRESH_TICKS = 10;
	/** Shadow cells coarsen with distance until they are about this fraction of a rendered pixel. 0 = off. Higher = coarser/faster. */
	static double SHADOW_LOD = 0.75;
	/** Faces fogged beyond this fraction skip AO/shadow/skylight. 1.0 = never skip. */
	static double FOG_SKIP = 0.97;
	/** Bumped whenever blocks or loaded chunks change; render caches clear themselves when it moves. */
	static volatile int worldVer;
	/** Shared ambient-occlusion strength for Classic and Modern; zero bypasses AO sampling. */
	static volatile double AO_STRENGTH = 0.5;
	static volatile int lightVer; // bumped when an emitting block is added/removed or everything is reloaded
	static boolean emits(byte b) { int i = b & 0xFF; return i < GLOW.length && GLOW[i] > 0; }
	static final LinkedHashMap<Long, Object> chunkCache = new LinkedHashMap<>();
	static int pendingCount;
	static long homeKey = World.NONE;
	static volatile long cacheBytes;
	static boolean generating;
	static volatile boolean[] OPAQUE = new boolean[256];
	static final ExecutorService savePool = Executors.newSingleThreadExecutor(r -> { Thread t = new Thread(r, "nexus-save"); t.setDaemon(true); return t; });
	static final AtomicBoolean saveInProgress = new AtomicBoolean(false);
	static volatile boolean saveRequested;
	static volatile File requestedSaveFile;
	static final Object SAVE_LOCK = new Object();
	static volatile boolean shutdownSaveStarted;
	// Bound background chunk generation so it cannot starve rendering or the main loop.
	static final ExecutorService genPool = Executors.newFixedThreadPool(GEN_THREADS, r -> {
		Thread t = new Thread(r, "nexus-gen");
		t.setDaemon(true);
		t.setPriority(2);
		return t;
	});

	static final class GenBatch {
		final long[][] coords;
		final List<Future<Octree>> futures;
		final boolean[] runFeatures;
		final boolean[] cachedRestore;
		final int epoch;
		GenBatch(long[][] coords, List<Future<Octree>> futures, boolean[] runFeatures, boolean[] cachedRestore, int epoch) {
			this.coords = coords; this.futures = futures; this.runFeatures = runFeatures;
			this.cachedRestore = cachedRestore; this.epoch = epoch;
		}
	}

	static GenBatch inFlight;
	static final ArrayDeque<long[]> featureQueue = new ArrayDeque<>();
	static int featureEpoch;
	static final long FEATURE_BUDGET_NS = 4_000_000L; // max feature-pass time per frame
	static final int AUTO_GUI_SCALE_WIDTH = 2000;
	static final double AUTO_FOCAL_MIN = 5;
	static final double AUTO_FOCAL_MAX = 1000;
	static final int AUTO_FOV_BASE_WIDTH = 856;
	static final int AUTO_FOV_REFERENCE_WIDTH = 2880;
	static final double AUTO_FOCAL_BASE = 90;
	static final double AUTO_FOCAL_REFERENCE = 250;
	static final double FOV_MIN = 1, FOV_MAX = 179;
	static int fovWidth = -1;
	static long lastChunkCleanup;
	static double red = 0.3, green = 0.4, blue = 0.5;
	static volatile boolean toggleFullscreenRequested;
	static final byte[] EMPTY = new byte[0];
	static final String[] NAMES = new String[BLOCK_COUNT];
	static final Color HOTBAR_BG = new Color(0x33, 0x33, 0x33, 0x7F).darker(), HOTBAR_BORDER = Color.gray.darker();
	static int page;
	static boolean titleIdle;
	static int zoomWidth = -1;
	static final int MAX_LOAD_PER_PASS = 64;
	final static byte AIR = 0, GRASS = 1, DIRT = 2, STONE = 3, BRICKS = 4, OAK_LOG = 5, LEAVES = 6, GLASS = 7,
			SLATE = 8, DYNAMITE = 9, SNOW = 10, MAGMA = 11, SAND = 12, ICE = 13, TOPAZ = 14, EMERALD = 15,
			RUBY = 16, SAPPHIRE = 17, AMETHYST = 18, COPPER = 19, IRON_ORE = 20, COPPER_ORE = 21, COAL_ORE = 22,
			OBSIDIAN = 23, CLAY = 24, GRAVEL = 25, OAK_PLANKS = 26, IRON = 27, COAL = 28, ASH = 29, CHECKERBOARD = 30,
			MOSS = 31, TANZANITE = 32, RHODONITE = 33, BASALT = 34, MARBLE = 35, BIRCH_LOG = 36, BIRCH_PLANKS = 37,
			RED_LEAVES = 38, ORANGE_LEAVES = 39, YELLOW_LEAVES = 40, AUTUMN_GRASS = 41, TILE = 42,
			GOLD = 43, GOLD_ORE = 44, DIAMOND = 45, QUARTZ = 46;
	static volatile int lightQ = 2;   // 0 basic, 1 AO + glow, 2 AO + skylight
	static volatile boolean lanternEnabled = false, blockLightingEnabled = true;
	static final String[] LIGHT_NAMES = { "Basic", "AO + Glow", "AO + Skylight" };
	static double caveMix;            // 0 = outside, 1 = deep underground (smoothed)
	static final float[] GLOW = glow();
	static final Map<Long, Object> savedChunks = new HashMap<>();
	/** When enabled, every chunk is retained in the active .nexus save and restored before regeneration. */
	static volatile boolean persistentStorage = false;
	static volatile File activeSaveFile;
	static long lastPersistentSave;
	private static final ThreadLocal<byte[]> GEN_DENSE = ThreadLocal.withInitial(() -> new byte[VOL]);
	private static int[] loadOrder;
	private static int loadOrderR = -1;
	static volatile int streamVer;                      // chunk load/unload/generation changes (throttled cache clear)
	static volatile long userTopY = Long.MAX_VALUE;     // highest (smallest y) block the player may have placed
	static final Semaphore finished = new Semaphore(0);
	private final Object paintLock = new Object();
	private static final ThreadLocal<byte[]> SAVE_DENSE = ThreadLocal.withInitial(() -> new byte[VOL]);
	private static final ThreadLocal<byte[]> SAVE_ENC = ThreadLocal.withInitial(() -> new byte[VOL * 2 + 16]);
	static final byte[][] PAGES = {
		{ GRASS, DIRT, STONE, BRICKS, OAK_LOG, LEAVES, GLASS, SLATE, OAK_PLANKS },
		{ DYNAMITE, TOPAZ, EMERALD, ICE, TANZANITE, RHODONITE, SNOW, SAND, ASH },
		{ BIRCH_LOG, BIRCH_PLANKS, RED_LEAVES, ORANGE_LEAVES, YELLOW_LEAVES, AUTUMN_GRASS, GOLD_ORE, GOLD, TILE },
		{ COAL_ORE, COPPER_ORE, IRON_ORE, COAL, COPPER, IRON, MAGMA, OBSIDIAN, MOSS },
		{ RUBY, SAPPHIRE, AMETHYST, DIAMOND, QUARTZ, CLAY, GRAVEL, BASALT, MARBLE },
		{ CHECKERBOARD, AIR, AIR, AIR, AIR, AIR, AIR, AIR, AIR }, };
	static final byte[] XOR_PAGE = { BRICKS, DIRT, GRASS, OAK_LOG, STONE, LEAVES, GLASS, SLATE, AIR };

	//  							RUBY      SAPPH     AMETH     COPPER    IRON ORE  COP_ORE   COAL ORE  OBSIDIAN
	static final int[] X_BASE   = { 0xD4123A, 0x1F4FE0, 0x9B3CD8, 0xDE774B, 0x7F7F7F, 0x7F7F7F, 0x7F7F7F, 0x1E1A2D,
	//  							CLAY      GRAVEL    PLANKS    IRON      COAL      ASH       TILE      MOSS
								  0xB4704F, 0x8C8C96, 0xCBA976, 0xEBCBAE, 0x303030, 0x5A5A5A, 0xFFFFFF, 0x5A8F3C,
	//                              TANZA     RHODO     BASALT    MARBLE    GOLD      G. ORE    DIAMOND   QUARTZ
								  0x403060, 0x803850, 0x343943, 0xE8E5DD, 0xFCC91C, 0x7F7F7F, 0x43CFE0, 0xE8E8EE };
	//								RUBY      SAPPH     AMETH     COPPER    IRON ORE  COP_ORE   COAL ORE  OBSIDIAN
	static final int[] X_ACCENT = { 0xFF9AB0, 0x9CC4FF, 0xE0B0FF, 0xF7A986, 0xE0B890, 0xC87850, 0x202020, 0x5A3C8C,
	//								CLAY      GRAVEL    PLANKS    IRON      COAL      ASH       TILE      MOSS
								 0xC88B6A, 0x5A5A64, 0xC29759, 0xF5E7DA, 0x505050, 0x5A5A5A, 0x2A2A2A, 0x8CC858,
    //	                           TANZA     RHODO     BASALT    MARBLE    GOLD      G. ORE    DIAMOND   QUARTZ
								 0xA080E0, 0xE080A0, 0x626A78, 0xFFFFFF, 0xFFA600, 0xFCC91C, 0xD8FFFF, 0xFFFFFF };
	static final int[] X_STYLE  = { 4, 4, 4, 3, 1, 1, 1, 1, 0, 1, 2, 3, 1, 0, 5, 1, 4, 4, 2, 1, 3, 1, 4, 4 };

	static {
		Random r = new Random(0);
		for (byte i = 0; i < perlinRes; i++) {
			PERLIN[i] = r.nextDouble();
		}
		for (byte cx = 0; cx < CROSS; cx++) {
			for (byte cy = 0; cy < CROSS; cy++) {
				int ax = Math.abs(cx - CROSS / 2) + 2, ay = Math.abs(cy - CROSS / 2) + 2;
				if (ax * ay < Math.sqrt(CROSS * CROSS / 2) && ax + ay < CROSS * 0.4375 && ax + ay > CROSS * 0.296875)
					crosshair.setRGB(cx, cy, 0xFFFFFFFF);
			}
		}
		for (int i = 0; i < RENDER_THREADS; i++)
			workers.add(new Render());
		NAMES[AIR] = "Air";       NAMES[GRASS] = "Grass";   NAMES[DIRT] = "Dirt";
		NAMES[STONE] = "Stone";   NAMES[BRICKS] = "Bricks"; NAMES[OAK_LOG] = "Oak Log";
		NAMES[LEAVES] = "Leaves"; NAMES[GLASS] = "Glass";   NAMES[SLATE] = "Slate";
		NAMES[DYNAMITE] = "Dynamite"; NAMES[SNOW] = "Snow"; NAMES[MAGMA] = "Magma";
		NAMES[SAND] = "Sand";     NAMES[ICE] = "Ice";       NAMES[TOPAZ] = "Topaz";
		NAMES[EMERALD] = "Emerald"; NAMES[RUBY] = "Ruby"; NAMES[SAPPHIRE] = "Sapphire"; NAMES[AMETHYST] = "Amethyst"; NAMES[COPPER] = "Copper";
		NAMES[IRON_ORE] = "Iron Ore"; NAMES[COPPER_ORE] = "Copper Ore"; NAMES[COAL_ORE] = "Coal Ore"; NAMES[OBSIDIAN] = "Obsidian";
		NAMES[CLAY] = "Clay"; NAMES[GRAVEL] = "Gravel"; NAMES[OAK_PLANKS] = "Oak Planks"; NAMES[IRON] = "Iron";
		NAMES[COAL] = "Coal"; NAMES[ASH] = "Ash"; NAMES[CHECKERBOARD] = "Checkerboard"; NAMES[MOSS] = "Moss";
		NAMES[TANZANITE] = "Tanzanite"; NAMES[RHODONITE] = "Rhodonite";
		NAMES[BASALT] = "Basalt"; NAMES[MARBLE] = "Marble"; NAMES[BIRCH_LOG] = "Birch Log"; NAMES[BIRCH_PLANKS] = "Birch Planks";
		NAMES[RED_LEAVES] = "Red Leaves"; NAMES[ORANGE_LEAVES] = "Orange Leaves"; NAMES[YELLOW_LEAVES] = "Yellow Leaves";
		NAMES[AUTUMN_GRASS] = "Autumn Grass"; NAMES[TILE] = "Tile"; NAMES[GOLD] = "Gold";
		NAMES[GOLD_ORE] = "Gold Ore"; NAMES[DIAMOND] = "Diamond"; NAMES[QUARTZ] = "Quartz";
	}
	// ======================= SURVIVAL =======================
	static volatile boolean survival = false, createSurvival = false, dead = false, deathConfirm = false, leftDown = false;
	static final int MAX_HEALTH = 5, INV_PAGES = 4, INV_SLOTS = 9, STACK_MAX = 99999;
	static final long DAMAGE_COOLDOWN_MS = 500;
	static final double FALL_SAFE = 15, FALL_EXTRA = 50; // 1 dmg at 15 blocks, +1 per extra 50
	static volatile int health = MAX_HEALTH;
	static long lastDamageMs;
	static double fallDist;
	static volatile int countFontSize = 12;                     // stack-count font (cycled in General Settings)
	static BasicStroke hotbarStroke = new BasicStroke(3);
	static final byte[][] invId = new byte[INV_PAGES][INV_SLOTS];
	static final int[][] invCount = new int[INV_PAGES][INV_SLOTS];

	// ---- block breaking ----
	static final int CAT_NATURE = 0, CAT_STONE = 1, CAT_SLATE = 2, CAT_METAL = 3, CAT_MAGMA = 4,
			CAT_OBSIDIAN = 5, CAT_DUSTY = 6, CAT_DIRTY = 7, CAT_GEM = 8;
	/** Seconds to break, indexed by CAT_*. Edit these to tune. Uncategorised blocks use the stone value. */
	static final double[] BREAK_SECONDS = { 0.30, 1.00, 1.40, 1.80, 2.00, 3.50, 0.25, 0.40, 1.60 };
	static volatile double breakSpeed = 1.0;                    // global multiplier (2 = twice as fast)
	static final int BREAK_STAGES = 5;
	static final byte[] BREAK_CAT = buildBreakCats();
	static final double[] CRACK_FRAC = { 0.10, 0.28, 0.50, 0.75, 1.0 };   // share of the crack pixels shown per stage
	static final boolean[][] CRACK = buildCracks();
	static volatile long breakX = NO_POS, breakY = NO_POS, breakZ = NO_POS;
	static volatile int breakStage = -1;
	static double breakProgress;
	static long lastBreakSoundMs;

	static byte[] buildBreakCats() {
		byte[] c = new byte[256];
		Arrays.fill(c, (byte) CAT_STONE);                       // default = stone speed
		for (byte b : new byte[] { GRASS, AUTUMN_GRASS, LEAVES, RED_LEAVES, ORANGE_LEAVES, YELLOW_LEAVES, MOSS }) c[b] = CAT_NATURE;
		for (byte b : new byte[] { STONE, COAL_ORE, COPPER_ORE, IRON_ORE, GOLD_ORE }) c[b] = CAT_STONE;
		c[SLATE] = CAT_SLATE;
		for (byte b : new byte[] { IRON, COPPER, GOLD }) c[b] = CAT_METAL;
		c[MAGMA] = CAT_MAGMA;
		c[OBSIDIAN] = CAT_OBSIDIAN;
		for (byte b : new byte[] { SAND, SNOW, ASH, GRAVEL }) c[b] = CAT_DUSTY;
		for (byte b : new byte[] { DIRT, CLAY }) c[b] = CAT_DIRTY;
		for (byte b = 1; b < BLOCK_COUNT; b++) if (kind(b) == 4) c[b] = CAT_GEM; // everything with the gem sound
		return c;
	}

	private static double cdist(int i) { double dx = i % 16 - 7.5, dy = i / 16 - 7.5; return dx * dx + dy * dy; }

	/** 8 arms radiate from the centre, 8 forks branch off them; pixels are then sorted centre-first so each stage grows outward. */
	static boolean[][] buildCracks() {
		Random r = new Random(100);
		boolean[] seen = new boolean[256];
		int[] order = new int[256];
		int n = 0;
		for (byte arm = 0; arm < 16; arm++) {
			double px = 7.5, py = 7.5, ang;
			int steps;
			if (arm < 8) { ang = arm * Math.PI / 4 + (r.nextDouble() - 0.5) * 0.6; steps = 16; }
			else {
				int k = r.nextInt(n);  // fork from an existing crack pixel
				px = order[k] & 15; py = order[k] / 16;
				ang = Math.atan2(py - 7.5, px - 7.5) + (r.nextBoolean() ? 1 : -1) * (0.5 + r.nextDouble() * 0.6);
				steps = 6 + r.nextInt(6);
			}
			for (int s = 0; s < steps; s++) {
				int ix = (int) Math.round(px), iy = (int) Math.round(py);
				if (ix < 0 || ix > 15 || iy < 0 || iy > 15) break;
				int i = iy * 16 + ix;
				if (!seen[i]) { seen[i] = true; order[n++] = i; }
				ang += (r.nextDouble() - 0.5) * 0.7;
				px += Math.cos(ang) * 0.7; py += Math.sin(ang) * 0.7;
			}
		}
		for (int a = 1; a < n; a++) { // insertion sort, nearest to centre first
			int v = order[a], b = a - 1;
			double dv = cdist(v);
			while (b >= 0 && cdist(order[b]) > dv) { order[b + 1] = order[b]; b--; }
			order[b + 1] = v;
		}
		boolean[][] m = new boolean[BREAK_STAGES][256];
		for (int st = 0; st < BREAK_STAGES; st++)
			for (int k = 0, upto = Math.max(1, (int) (n * CRACK_FRAC[st])); k < upto && k < n; k++) m[st][order[k]] = true;
		return m;
	}

	/** Called from Render.march for the block being broken. u,v = texel 0..15. */
	static int crackOverlay(int c, int u, int v, int stage) {
		if (!CRACK[stage][v * 16 + u]) return c;
		return (c & 0xFF000000) | ((c >> 16 & 0xFF) * 2 / 5) << 16 | ((c >> 8 & 0xFF) * 2 / 5) << 8 | ((c & 0xFF) * 2 / 5);
	}

	static double breakSeconds(byte id) {
		return BREAK_SECONDS[BREAK_CAT[id & 0xFF]] / Math.max(0.01, breakSpeed);
	}

	static void resetBreak() {
		breakStage = -1; breakProgress = 0;
		breakX = breakY = breakZ = NO_POS; lastBreakSoundMs = 0;
	}

	/** Main thread, once per 10 ms tick: hold-to-break. Letting go (or looking away) resets to the normal stage. */
	static void survivalBreakTick() {
		final long hx = hoveredX, hy = hoveredY, hz = hoveredZ;
		if (!survival || dead || !leftDown || fill || paused || dialogOpen || mainMenu || hy == NO_POS) { if (breakStage >= 0 || breakProgress != 0) resetBreak(); return; }
		if (hx != breakX || hy != breakY || hz != breakZ) { resetBreak(); breakX = hx; breakY = hy; breakZ = hz; lastBreakSoundMs = System.currentTimeMillis(); }
		final byte id = getBlock(hx, hy, hz);
		if (id == AIR) { resetBreak(); return; }
		long now = System.currentTimeMillis();
		if (now - lastBreakSoundMs >= 500) { block(id, 2, hx, hy, hz); lastBreakSoundMs = now; }
		breakProgress += (TICK_NS / 1e9) / breakSeconds(id);
		if (breakProgress >= 1.0) { finishBreak(hx, hy, hz, id); resetBreak(); return; }
		breakStage = Math.min(BREAK_STAGES - 1, (int) (breakProgress * BREAK_STAGES));
	}

	private static void finishBreak(long bx, long by, long bz, byte id) {
		block(id, 0, bx, by, bz);
		Particles.burst(bx, by, bz, id, 14, 0.04);
		setBlock(bx, by, bz, AIR);
		if (giveBlock(id, 1) > 0) say("Inventory full");
	}

	// ---- health ----
	static volatile int flashFrom, flashTo;
	static volatile long flashUntil;

	static void damage(int pts) {
		if (!survival || dead || pts <= 0) return;
		long now = System.currentTimeMillis();
		if (now - lastDamageMs < DAMAGE_COOLDOWN_MS) return;
		lastDamageMs = now;
		int old = health;
		health = Math.max(0, old - pts);
		flashTo = now < flashUntil ? Math.max(flashTo, old) : old; // merge with a flash that is still showing
		flashFrom = health;
		flashUntil = now + 333;
		if (sound && hurt != null) play(hurt, 1.0);
		if (health == 0) die();
	}

	static void die() {
		dead = true; deathConfirm = false; leftDown = false;
		synchronized (input) { input.clear(); }
		velX = velY = velZ = 0; sprint = false;
		resetBreak();
		lock = false; mouseLookArmed = false;
		SwingUtilities.invokeLater(() -> frame.setCursor(Cursor.getDefaultCursor()));
	}

	private static void checkDamage(byte below, double vy0, boolean wasStuck) {
		if (!survival) return;
		survivalBreakTick();
		if (dead) { fallDist = 0; return; }
		double dy = diff(y, prevY);                              // +y is down
		if (fly || wasStuck || dy < 0) fallDist = 0; else fallDist += dy;
		if (vy0 > 0 && velY <= 0) {                              // landed this tick
			if (fallDist >= FALL_SAFE) damage(1 + (int) ((fallDist - FALL_SAFE) / FALL_EXTRA));
			fallDist = 0;
		}
		if (below == MAGMA) damage(1);
		long now = System.currentTimeMillis();
		if (!dead && health < MAX_HEALTH && now - lastDamageMs >= 30_000L) {
			health++;
			lastDamageMs = now; // another point can regenerate after the next 30 damage-free seconds
		}
	}

	static void resetSurvivalState() {
		flashUntil = 0;
		for (int p = 0; p < INV_PAGES; p++) { Arrays.fill(invId[p], AIR); Arrays.fill(invCount[p], 0); }
		health = MAX_HEALTH; dead = false; deathConfirm = false; page = 0; heldBlock = 0;
		fallDist = 0; lastDamageMs = System.currentTimeMillis(); leftDown = false;
		resetBreak();
	}

	/** Applies the survival block of a loaded save. */
	private static void applySurvivalState(boolean s, double flightSpeed, int hp, byte[][] ids, int[][] cnt) {
		flashUntil = 0;
		survival = s;
		if (flightSpeed > 0 && Double.isFinite(flightSpeed)) flight = flightSpeed;
		for (int p = 0; p < INV_PAGES; p++) { System.arraycopy(ids[p], 0, invId[p], 0, INV_SLOTS); System.arraycopy(cnt[p], 0, invCount[p], 0, INV_SLOTS); }
		health = Math.max(0, Math.min(MAX_HEALTH, hp));
		dead = s && hp <= 0; deathConfirm = false; page = 0; heldBlock = 0;
		fallDist = 0; lastDamageMs = System.currentTimeMillis(); leftDown = false;
		resetBreak();
		if (s) fly = false;
	}

	/** Respawn: world spawn -> nearby spot -> random spot (repairSavedSpawnIfBlocked also saves the new spawn). */
	static void respawn() {
		flashUntil = 0;
		flushDirty();                                            // so player edits are visible to the obstruction check
		repairSavedSpawnIfBlocked();
		health = MAX_HEALTH; dead = false; deathConfirm = false; fallDist = 0; lastDamageMs = System.currentTimeMillis(); fly = false;
		resetBreak();
		moveTo(copyOf(worldSpawnX), copyOf(worldSpawnY), copyOf(worldSpawnZ), true);
		lock = true; mouseLookArmed = false;
		frame.setCursor(hidden);
		center();
	}

	// ---- inventory ----
	static int pageCount() { return survival ? INV_PAGES : PAGES.length; }

	static byte[][] copyIds(byte[][] a) { byte[][] c = new byte[a.length][]; for (int i = 0; i < a.length; i++) c[i] = a[i].clone(); return c; }
	static int[][] copyCounts(int[][] a) { int[][] c = new int[a.length][]; for (int i = 0; i < a.length; i++) c[i] = a[i].clone(); return c; }

	/** Adds n blocks to the given inventory (existing stacks first, then empty slots, current hotbar first). Returns how many did NOT fit. */
	static int giveTo(byte[][] ids, int[][] cnt, byte id, int n) {
		if (id == AIR || n <= 0) return 0;
		final int pages = ids.length;
		for (int k = 0; k < pages && n > 0; k++) {
			int p = (page + k) % pages;
			for (int i = 0; i < INV_SLOTS && n > 0; i++)
				if (ids[p][i] == id && cnt[p][i] < STACK_MAX) { int add = Math.min(n, STACK_MAX - cnt[p][i]); cnt[p][i] += add; n -= add; }
		}
		for (int k = 0; k < pages && n > 0; k++) {
			int p = (page + k) % pages;
			for (int i = 0; i < INV_SLOTS && n > 0; i++)
				if (ids[p][i] == AIR) { int add = Math.min(n, STACK_MAX); ids[p][i] = id; cnt[p][i] = add; n -= add; }
		}
		return n;
	}

	/** Removes n blocks. Returns how many could NOT be removed. */
	static int takeFrom(byte[][] ids, int[][] cnt, byte id, int n) {
		for (int p = 0; p < ids.length && n > 0; p++)
			for (int i = 0; i < INV_SLOTS && n > 0; i++)
				if (ids[p][i] == id) { int t = Math.min(n, cnt[p][i]); cnt[p][i] -= t; n -= t; if (cnt[p][i] == 0) ids[p][i] = AIR; }
		return n;
	}

	static int giveBlock(byte id, int n) { return giveTo(invId, invCount, id, n); }

	static void consumeHeld() {
		int p = page % INV_PAGES;
		if (--invCount[p][heldBlock] <= 0) { invCount[p][heldBlock] = 0; invId[p][heldBlock] = AIR; }
	}

	/**
	 * All-or-nothing inventory transaction for fill/copy: removes need[id], adds repl[id].
	 * Works on clones first, so on failure nothing changes.
	 */
	static boolean commitInventory(long[] need, long[] repl) {
		byte[][] ids = copyIds(invId); int[][] cnt = copyCounts(invCount);
		for (int id = 1; id < 256; id++)
			if (need[id] > 0 && takeFrom(ids, cnt, (byte) id, (int) Math.min(Integer.MAX_VALUE, need[id])) > 0) {
				say("Not enough " + getType((byte) id) + " (" + need[id] + " needed)");
				return false;
			}
		for (int id = 1; id < 256; id++)
			if (repl[id] > 0 && giveTo(ids, cnt, (byte) id, (int) Math.min(Integer.MAX_VALUE, repl[id])) > 0) {
				say("Inventory full - nothing changed");
				return false;
			}
		for (int p = 0; p < INV_PAGES; p++) { System.arraycopy(ids[p], 0, invId[p], 0, INV_SLOTS); System.arraycopy(cnt[p], 0, invCount[p], 0, INV_SLOTS); }
		return true;
	}

	private static boolean isLoaded(long x, long y, long z) {
		return world.chunk(x >> SHIFT, y >> SHIFT, z >> SHIFT) != World.UNLOADED;
	}

	/** Survival fill: costs one held-type block per changed voxel, refunds every block it replaces. */
	private static void fillFromInventory(byte block, long x0, long y0, long z0, long x1, long y1, long z1) {
		long[] need = new long[256], repl = new long[256];
		for (long a = x0; a < x1; a++)
			for (long b = y0; b < y1; b++)
				for (long c = z0; c < z1; c++) {
					if (!isLoaded(a, b, c)) continue;
					byte cur = getBlock(a, b, c);
					if (cur == block) continue;
					if (block != AIR) need[block & 0xFF]++;
					if (cur != AIR) repl[cur & 0xFF]++;
				}
		if (!commitInventory(need, repl)) return;
		fill(block, x0, y0, z0, x1, y1, z1, true);
		chunkDirty = true;
	}
	static final Map<Long, LinkedHashSet<Long>> pendingWrites = new LinkedHashMap<>();
	static final int PENDING_MAX = 1_000_000;

	public static void main(String[] args) {
		Runtime.getRuntime().addShutdownHook(new Thread(Nexus::saveOnShutdown, "nexus-shutdown-save"));
		frame = new JFrame("Bitwise Nexus " + VERSION);
		Nexus nexus = new Nexus();
		frame.setSize(width, height);
		frame.setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
		frame.addWindowListener(new WindowAdapter() { @Override public void windowClosing(WindowEvent e) { if (persistentStorage && activeSaveFile != null) { saveRequested = true; requestedSaveFile = activeSaveFile; } Nexus.saveOnShutdown(); frame.dispose(); System.exit(0); } });
		frame.setLocationRelativeTo(null);
		hidden = frame.getToolkit().createCustomCursor(new BufferedImage(1, 1, 2), new Point(), null);
		frame.setCursor(Cursor.getDefaultCursor());
		lock = false;
		frame.addKeyListener(nexus);
		frame.addMouseListener(nexus);
		frame.addMouseMotionListener(nexus);
		frame.addFocusListener(nexus);
		frame.addMouseWheelListener(nexus);
		frame.addComponentListener(new ComponentAdapter() {
			@Override
			public void componentResized(ComponentEvent e) {
				width = Math.max(8, frame.getContentPane().getWidth());
				height = Math.max(8, frame.getContentPane().getHeight());
				update = true; // handled on the main loop thread (no more races / thread leaks)
			}
		});
		frame.getContentPane().add(nexus);
		frame.setVisible(true);
		nexus.run();
	}

	static boolean isLeaves(byte b) {
		return b == LEAVES || b == RED_LEAVES || b == ORANGE_LEAVES || b == YELLOW_LEAVES;
	}

	private static int leafTint(int type, int x, int y, double pNoise) {
		int light, dark;
		switch (type) {
		case RED_LEAVES:    light = 0xE03020; dark = 0xA82016; break;
		case ORANGE_LEAVES: light = 0xFF8A1A; dark = 0xCC6A10; break;
		case YELLOW_LEAVES: light = 0xF2D21C; dark = 0xC4A810; break;
		default:            light = 0x00FF00; dark = 0x00CC00; break;
		}
		double dx = Math.abs((x & 3) - 2) * 2;
		double dy = (y & 7) - 4;
		if ((y / 8 & 1) == 1)
			dx = Math.abs((x + 2 & 3) - 2) * 2;
		dx += pNoise;
		double d = dx + Math.abs(dy);
		if (dy < 0)
			d = Math.sqrt(dx * dx + dy * dy);
		return d < 3.5 ? light : d < 4 ? dark : 0;
	}

	/** Light a block emits on its own (added on top of normal lighting). */
	static float[] glow() {
		float[] a = new float[BLOCK_COUNT];
		a[MAGMA] = 0.9f; a[RUBY] = 0.3f; a[AMETHYST] = 0.3f; a[SAPPHIRE] = 0.25f;
		a[TOPAZ] = 0.25f; a[DIAMOND] = 0.25f; a[EMERALD] = 0.2f; a[DYNAMITE] = 0.05f;
		a[TANZANITE] = 0.2f; a[RHODONITE] = 0.2f; a[QUARTZ] = 0.15f;
		return a;
	}

	private static long caveCheckX = Long.MIN_VALUE, caveCheckY, caveCheckZ;
	static volatile boolean caveSnap;
	private static double caveTarget;
	static int lastLoadRadius = -1;
	static long[] CAND = new long[0];

	/** True once every chunk in the column between loadTop and the player is loaded. */
	private static boolean caveColumnLoaded(long bx, long by, long bz, long loadTop) {
		long cx = bx >> SHIFT, cz = bz >> SHIFT;
		for (long cy = loadTop >> SHIFT; cy <= by >> SHIFT; cy++)
			if (world.chunk(cx, cy, cz) == World.UNLOADED)
				return false;
		return true;
	}

	/** Underground fog is opaque by dist / 1.5, so far chunks cannot be seen. */
	static int effectiveRadius() {
		return caveMix > 0.95 ? Math.max(1, Math.min(radius, (int) Math.ceil(dist / (1.5 * SIZE)))) : radius;
	}

	static void updateCaveMix() {
		long bx = floorOf(viewX), by = floorOf(viewY), bz = floorOf(viewZ);
		long top = topBound();
		long scanTop = Math.max(top, (chunkOf(viewY) - radius) * SIZE); // whole vertical render range
		if (by <= scanTop) {
			if (caveSnap) { caveMix = caveTarget; caveSnap = false; }
			else caveMix += (caveTarget - caveMix) * 0.04;
			return;
		}
		if (bx != caveCheckX || by != caveCheckY || bz != caveCheckZ) {
			// Underground the loader only keeps effectiveRadius() chunks loaded, so only require those.
			long loadTop = Math.max(scanTop, (chunkOf(viewY) - effectiveRadius()) * SIZE);
			if (!caveColumnLoaded(bx, by, bz, loadTop)) {
				caveCheckX = Long.MIN_VALUE;
				caveMix += (caveTarget - caveMix) * 0.04;
				return;
			}
			caveCheckX = bx; caveCheckY = by; caveCheckZ = bz;
			int roofBlocks = columnRoof(bx, by, bz, scanTop);
			int coveredNeighbours = 0;
			for (int dx = -1; dx <= 1; dx++)
				for (int dz = -1; dz <= 1; dz++) {
					if (dx == 0 && dz == 0) continue;
					if (columnRoof(bx + dx, by, bz + dz, scanTop) >= CAVE_NEIGH_ROOF)
						coveredNeighbours++;
				}
			if (caveTarget < 0.5)
				caveTarget = roofBlocks >= CAVE_ROOF_ENTER && coveredNeighbours >= 5 ? 1 : 0;
			else
				caveTarget = roofBlocks >= CAVE_ROOF_STAY && coveredNeighbours >= 2 ? 1 : 0;
			if (caveSnap) { caveMix = caveTarget; caveSnap = false; }
		}
		caveMix += (caveTarget - caveMix) * 0.04;
	}

	static final int CAVE_ROOF_ENTER = 64, CAVE_ROOF_STAY = 40, CAVE_NEIGH_ROOF = 48, CAVE_ROOF_CAP = 128;

	/** Counts solid blocks above (bx, by, bz) all the way up to scanTop (the top of the vertical render range), capped. */
	private static int columnRoof(long bx, long by, long bz, long scanTop) {
		int roof = 0;
		long yy = by - 1;
		while (yy >= scanTop) {
			Octree c = world.chunk(bx >> SHIFT, yy >> SHIFT, bz >> SHIFT);
			long lo = Math.max(scanTop, (yy >> SHIFT) << SHIFT);
			if (c != null && c != World.UNLOADED) {
				for (; yy >= lo; yy--) {
					byte b = c.get((byte) (bx & MASK), (byte) (yy & MASK), (byte) (bz & MASK));
					if (b == AIR || isLeaves(b) || b == GLASS) continue;
					if (++roof >= CAVE_ROOF_CAP) return roof;
				}
			} else
				yy = lo - 1; // empty or unloaded chunk: jump to the next one
		}
		return roof;
	}

	/** Wrappers so Fog (a separate class) can reach the private noise helpers. */
	static double biomeVal(double wx, double wz) { return noise(wx / 512.0, wz / 512.0); }
	static double zone(int biome, long x, long y, long z) { return zoneAt(biome, x, y, z); }

	private static int[] dataOf(BufferedImage img) {
		return ((DataBufferInt) img.getRaster().getDataBuffer()).getData();
	}

	private static void allocateBuffers(int w, int h) {
		screen = new BufferedImage(w, h, 1);
		backImg = new BufferedImage(w, h, 1);
		buffer = dataOf(backImg);
	}

	/** Show the finished frame and start drawing the next one into the other image. */
	private static void swapBuffers() {
		BufferedImage done = backImg;
		backImg = screen;
		screen = done;
		buffer = dataOf(backImg);
	}

	/** Runs the fixed 10 ms ticks that are due and records how far we are into the next one. */
	private static long runTicks(long clock) {
		long now = System.nanoTime();
		if (now - clock > 25 * TICK_NS) // don't spiral after a stall
			clock = now - 25 * TICK_NS;
		long ms = System.currentTimeMillis();
		while (now - clock > TICK_NS) {
			clock += TICK_NS;
			savePrev();
			tick(ms);
		}
		renderAlpha = Math.max(0, Math.min(1, (now - clock) / (double) TICK_NS));
		return clock;
	}

	private static void blend(SplitDecimal from, SplitDecimal to, SplitDecimal out) {
		double d = diff(to, from);            // small, so exact even at 2^60
		if (Math.abs(d) > TELEPORT) {         // respawn, load, dialog: don't slide across the map
			out.set(to);
			return;
		}
		TMP.setValue(d * renderAlpha);
		from.add(TMP, out);
	}

	private static void updateView() {
		blend(prevX, x, viewX);
		blend(prevY, y, viewY);
		blend(prevZ, z, viewZ);
		if (guiEnabled) updateHudSnapshot();
	}

	private static void savePrev() {
		prevX.set(x);
		prevY.set(y);
		prevZ.set(z);
	}

	private static int cachedRate = 60;
	private static long rateStamp;

	private static int getRefreshRate() {
		long n = System.currentTimeMillis();
		if (n - rateStamp > 30000) {
			rateStamp = n;
			int rate = GraphicsEnvironment.getLocalGraphicsEnvironment().getDefaultScreenDevice().getDisplayMode().getRefreshRate();
			cachedRate = rate > 0 && rate < 1000 ? rate : 60;
		}
		return cachedRate;
	}

	private static void limitFrame(long frameStartNs) {
	    if (!vSync)
	        return;

	    long frameDurationNs = 1_000_000_000L / getRefreshRate();
	    long deadline = frameStartNs + frameDurationNs;

	    while (true) {
	        long remaining = deadline - System.nanoTime();
	        if (remaining <= 0)
	            break;

	        if (remaining > 2_000_000L) {
	            LockSupport.parkNanos(remaining - 1_000_000L);
	        } else {
	            Thread.yield();
	        }
	    }
	}

	static String getType(byte block) {
		if (block < 0 || block >= BLOCK_COUNT) return "Unknown";
		String n = NAMES[block];
		return n != null ? n : "Block " + block;
	}

	private static long sizeOf(Object o) {
		return (o instanceof Octree ? ((Octree) o).memoryBytes() : ((byte[]) o).length + 16) + 64; // + map entry
	}

	static void clearSaved() {
		userTopY = Long.MAX_VALUE;
		savedChunks.clear();
		chunkCache.clear();
		cacheBytes = 0;
		pendingWrites.clear();
		pendingCount = 0;
	}

	/** Evict oldest regenerable chunks until both limits are satisfied. Safe to call any time (main thread). */
	static void evictCache() {
		int maxN = CACHE_MAX_CHUNKS;
		long maxB = CACHE_MAX_BYTES;
		if (maxN <= 0 && maxB <= 0)
			return;
		Iterator<Map.Entry<Long, Object>> it = chunkCache.entrySet().iterator();
		while (it.hasNext() && ((maxN > 0 && chunkCache.size() > maxN) || (maxB > 0 && cacheBytes > maxB))) {
			cacheBytes -= sizeOf(it.next().getValue());
			it.remove();
		}
	}

	static void stash(long key, Octree data, boolean user) {
		Object v;
		if (data == null) {
			v = EMPTY;
		} else {
			data.compact();
			v = data;
		}
		Object old = chunkCache.remove(key);
		if (old != null)
			cacheBytes -= sizeOf(old);
		if (user || savedChunks.containsKey(key)) { // player-edited: permanent
			dropPending(key);
			userTopY = Math.min(userTopY, World.unpackY(key) * SIZE);
			savedChunks.put(key, v);
			return;
		}
		chunkCache.put(key, v); // re-inserted at the newest end
		cacheBytes += sizeOf(v);
		evictCache();
	}

	/** Persist (if edited) and unload one ring slot. */
	static void unloadSlot(int s) {
		long k = world.keys[s];
		if (k == World.NONE)
			return;
		// Only retain chunks that contain player-made block changes.
		if (world.user[s])
			stash(k, world.data[s], true);
		world.keys[s] = World.NONE;
		world.data[s] = null;
		world.dirty[s] = false;
		world.user[s] = false;
	}

	/** Keep player edits across a clear/resize/save. Generation-only edits are simply regenerated. */
	static void flushDirty() {
		for (int s = 0; s < world.keys.length; s++)
			if (world.keys[s] != World.NONE && world.dirty[s] && world.user[s]) {
				stash(world.keys[s], world.data[s], true);
				world.dirty[s] = false;
			}
	}

	/** Cold-storage entry (Octree, or RLE bytes from a file) back to a live chunk. */
	static Octree restore(Object saved) {
		if (saved instanceof Octree)
			return (Octree) saved;
		byte[] b = (byte[]) saved;
		return b.length == 0 ? null : Octree.build(decodeInto(b, GEN_DENSE.get()));
	}

	static byte[] blobOf(Object o) {
		if (o instanceof byte[]) return (byte[]) o;
		byte[] dense = SAVE_DENSE.get();
		((Octree) o).toDense(dense);
		return encode(dense);
	}

	static byte[] decodeInto(byte[] data, byte[] out) {
		Arrays.fill(out, (byte) 0);
		int n = 0, i = 0;
		while (i < data.length && n < VOL) {
			byte v = data[i++];
			int run = 0;
			for (int shift = 0; i < data.length; shift += 7) {
				int b = data[i++] & 0xFF;
				run |= (b & 0x7F) << shift;
				if (b < 0x80 || shift >= 21)
					break;
			}
			int end = Math.min(VOL, n + run);
			if (v != 0 && end > n)
				Arrays.fill(out, n, end, v);
			n = end;
		}
		return out;
	}

	static int autoGuiScale(int windowWidth) {
		return windowWidth > AUTO_GUI_SCALE_WIDTH ? 2 : 1;
	}

	static double autoFov(int windowWidth) {
		double t = (windowWidth - AUTO_FOV_BASE_WIDTH) / (double) (AUTO_FOV_REFERENCE_WIDTH - AUTO_FOV_BASE_WIDTH);
		double value = AUTO_FOCAL_BASE + (AUTO_FOCAL_REFERENCE - AUTO_FOCAL_BASE) * t;
		value = Math.round(value / 5.0) * 5.0;
		value = Math.max(AUTO_FOCAL_MIN, Math.min(AUTO_FOCAL_MAX, value));
		return Math.toDegrees(2 * Math.atan(windowWidth / (8.0 * value)));
	}

	/** Set the true horizontal field of view (degrees, 0-180) and the projection scale derived from it. */
	static void setFov(double degrees) {
		fov = Math.max(FOV_MIN, Math.min(FOV_MAX, degrees));
		focal = Math.max(8, width) / (8.0 * Math.tan(Math.toRadians(fov) / 2));
	}

	// ------------------------------------------------------------------ helpers

	/** Toggle fullscreen while preserving the windowed size and position. */
	static void toggleFullscreen() {
	    GraphicsDevice device = GraphicsEnvironment.getLocalGraphicsEnvironment().getDefaultScreenDevice();

	    if (!fullscreen) {
	        windowedWidth = Math.max(8, frame.getWidth());
	        windowedHeight = Math.max(8, frame.getHeight());
	        windowedLocation = frame.getLocation();
	        fullscreen = true;
	        frame.dispose();
	        frame.setUndecorated(true);
	        frame.setResizable(false);
	        device.setFullScreenWindow(frame);
	        frame.setVisible(true);
	    } else {
	        fullscreen = false;
	        device.setFullScreenWindow(null);
	        frame.dispose();
	        frame.setUndecorated(false);
	        frame.setResizable(true);
	        frame.setSize(windowedWidth, windowedHeight);
	        if (windowedLocation != null)
	            frame.setLocation(windowedLocation);
	        else
	            frame.setLocationRelativeTo(null);
	        frame.setVisible(true);
	    }
	    width = Math.max(8, frame.getContentPane().getWidth());
	    height = Math.max(8, frame.getContentPane().getHeight());
	    update = true;
	    frame.toFront();
	    frame.requestFocus();
	    frame.requestFocusInWindow();
	    center();
	}

	static boolean key(int c) {
		synchronized (input) {
			return input.get(c);
		}
	}

	/** True once per `gap` ms while the key is held. */
	static boolean fire(int code, long gap) {
		long n = System.currentTimeMillis();
		if (key(code) && n - cool[code] >= gap) {
			cool[code] = n;
			return true;
		}
		return false;
	}

	static long chunkOf(double v) {
		return (long) Math.floor(v) >> SHIFT;
	}

	private static int b2i(boolean b) {
		return b ? 1 : 0;
	}

	/** Render distance changes resize the chunk ring, so they must run on the main loop thread. */
	static void requestDist(int d) {
		tasks.add(() -> setDist(d));
	}


	/** Flips XOR mode and rebuilds the atlas on the main thread, between frames. */
	void toggleXor() {
		tasks.add(() -> {
			xor = !xor;
			textures();
			repaint();
		});
	}

	static void setDist(int d) {
		dist = (short) Math.max(16, Math.min(4096, d));
		short r = (short) ((dist + SIZE - 1) / SIZE);
		if (r != radius) {
			flushDirty();
			radius = r;
			world.resize(r);
		}
		chunkDirty = true;
	}

	static volatile boolean sound = true;
	static final int RATE = 22050, KINDS = 8, VAR = 3;
	// kind: tone Hz, tone mix, noise lowpass, decay/s
	static final double[][] KIND = {
		{  80, .75, .30, 26 },  // 0 most stone types
		{  80, .55, .12, 22 },  // 1 dirt/clay/gravel/snow
		{  50, .50, .95, 20 },  // 2 grass/leaves/moss
		{ 100, .90, .28, 34 },  // 3 wood
		{1000, .75, .90, 14 },  // 4 glass/ice/gems
		{   0,   0, .75, 16 },  // 5 sand/ash
		{ 220, .90, .45, 10 },  // 6 metal
		{  55, .50, .08, 12 } };// 7 magma/glass/obsidian
	static final double[] LEN = { .22, .14, .09 }, VOLUME = { 1, .8, .35 }, PITCH = { 1, 1.25, .8 }; // break, place, step
	static final float[][] bank = new float[KINDS * 3 * VAR][];
	static final List<Voice> voices = new ArrayList<>();
	static final Random RND = new Random();
	static float[] boom;
	static volatile MusicVoice musicVoice;
	static double walked;

	static final class Voice {
		final float[] s; final float v; int p;
		Voice(float[] s, float v) { this.s = s; this.v = v; }
	}

	static int kind(byte b) {
		switch (b) {
		case DIRT: case CLAY: case GRAVEL: case SNOW: return 1;
		case GRASS: case LEAVES: case MOSS: case RED_LEAVES: case ORANGE_LEAVES: case YELLOW_LEAVES: case AUTUMN_GRASS: return 2;
		case OAK_LOG: case OAK_PLANKS: case BIRCH_LOG: case BIRCH_PLANKS: return 3;
		case ICE: case TOPAZ: case EMERALD: case RUBY: case SAPPHIRE: case AMETHYST: case TANZANITE: case RHODONITE: case DIAMOND: case QUARTZ: return 4;
		case SAND: case ASH: return 5;
		case IRON: case COPPER: case GOLD: return 6;
		case MAGMA: case GLASS: case OBSIDIAN: return 7;
		default: return 0;
		}
	}

	static float[] make(double[] k, double len, double pitch, long seed) {
		int n = (int) (RATE * len);
		float[] s = new float[n];
		Random r = new Random(seed);
		double lp = k[2], gain = Math.sqrt((2 - lp) / lp) * 0.5, f = k[0] * pitch, lo = 0;
		for (int i = 0; i < n; i++) {
			double t = i / (double) RATE, env = Math.exp(-t * k[3]) * (1 - i / (double) n) * Math.min(1, i / 40.0);
			lo += lp * (r.nextDouble() * 2 - 1 - lo);
			double tone = f > 0 ? Math.sin(6.2832 * f * t) + 0.4 * Math.sin(6.2832 * f * 2.76 * t) : 0;
			s[i] = (float) ((lo * gain * (1 - k[1]) + tone * k[1] * 0.6) * env);
		}
		return s;
	}

	static void init() {
		for (int k = 0; k < KINDS; k++)
			for (int a = 0; a < 3; a++)
				for (int v = 0; v < VAR; v++)
					bank[(k * 3 + a) * VAR + v] = make(KIND[k], LEN[a] * (k == 4 || k == 6 ? 1.8 : 1), PITCH[a] * (0.88 + 0.12 * v), k * 100 + a * 10 + v);
		boom = make(new double[] { 45, .45, .06, 3.5 }, 1.2, 1, 0);
		hurt = makeHurt();
		Thread t = new Thread(Nexus::mixer, "nexus-audio");
		t.setDaemon(true);
		t.start();
		Thread music = new Thread(Nexus::musicLoop, "nexus-bytebeat");
		music.setDaemon(true);
		music.setPriority(1);
		music.start();
	}

	static final int BB_MAX_SECONDS = 180; // Let each bytebeat track develop for three minutes before fading out.
	static final int BB_FADE_IN_SECONDS = 5;

	static final String FIRST_TRACK = "arpeggiator fun";
	static final double RARE_CHANCE = 0.1; // chance a pick comes from the rare tracks

	static final String[][] BYTEBEAT = { // name, author, rate, rare("1")
		{ "Useless1", "Decent-Manager-6169", "35280", "0" },
		{ "e", "absolute197", "46000", "0" },
		{ "qai", "lhphr", "44100", "0" },
		{ "ÐiskΩtroÑ", "lhphr", "9930", "0" },
		{ "Steady On Tim, It's Only A Budget Game", "Gasman", "44100", "0" },
		{ "Crystal Cave", "kOLbOSa_exe", "8000", "0" },
		{ "Phantasie für drei Blockflöten, Op. 256", "Algorias", "44100", "1" },
		{ "arpeggiator fun", "SArpnt", "44100", "0" },
		{ "Chase in the Forest", "SthephanShi", "44100", "0" },
		{ "echo_testing", "BaenHoHoHo", "32000", "1" },
		{ "Random Bytebeat Loop Song", "HypernovaHeathen", "48000", "1" }
	};

	static final class MusicVoice {
		final short[] samples;
		final int rate, loopSamples, fadeIn, fadeOut, extraLoop;
		long position; // output-rate frames
		MusicVoice(short[] samples, int loopSamples, int rate) {
			this.samples = samples; this.loopSamples = loopSamples; this.rate = rate;
			this.fadeIn = rate * BB_FADE_IN_SECONDS;
			this.extraLoop = 0; // Do not restart the track at its beginning just to fade it out.
			this.fadeOut = rate * 8; // Smooth eight-second fade at the end.
		}
		boolean finished() { return position * (long) rate / RATE >= (long) loopSamples + extraLoop; }
	}

	static float[] hurt;

	/** Short low "oof": falling sawtooth + a puff of low-passed noise, fast decay. */
	static float[] makeHurt() {
		int n = (int) (RATE * 0.30);
		float[] s = new float[n];
		Random r = new Random(77);
		double phase = 0, lo = 0;
		for (int i = 0; i < n; i++) {
			double t = i / (double) RATE;
			double f = Math.max(90, 260 - 480 * t);
			phase += f / RATE;
			double saw = (phase % 1.0) * 2 - 1;
			lo += 0.35 * (r.nextDouble() * 2 - 1 - lo);
			double env = Math.exp(-t * 9) * Math.min(1, i / 60.0);
			s[i] = (float) ((saw * 0.40 + lo * 0.45) * env);
		}
		return s;
	}

	static final ArrayList<Integer> bagRegular = new ArrayList<>(), bagRare = new ArrayList<>();
	static int lastTrack = -1;

	static int trackIndex(String name) {
		for (int i = 0; i < BYTEBEAT.length; i++) if (BYTEBEAT[i][0].equals(name)) return i;
		return 0;
	}

	/** Shuffle bag: every track plays once before any repeats, and never twice in a row. */
	static void refill(ArrayList<Integer> bag, boolean rare, int exclude) {
		for (int i = 0; i < BYTEBEAT.length; i++)
			if ("1".equals(BYTEBEAT[i][3]) == rare && i != exclude) bag.add(i);
		Collections.shuffle(bag, RND);
		int n = bag.size();
		if (n > 1 && bag.get(n - 1) == lastTrack) Collections.swap(bag, n - 1, 0);
	}

	static int draw(ArrayList<Integer> bag, boolean rare) {
		if (bag.isEmpty()) refill(bag, rare, -1);
		return bag.isEmpty() ? -1 : bag.remove(bag.size() - 1);
	}

	static int nextTrack() {
		int pick = -1;
		if (lastTrack < 0) { pick = trackIndex(FIRST_TRACK); refill(bagRegular, false, pick); }
		else if (RND.nextDouble() < RARE_CHANCE) pick = draw(bagRare, true);
		if (pick < 0) pick = draw(bagRegular, false);
		return lastTrack = pick;
	}

	static void musicLoop() {
		try { Thread.sleep(60000); } catch (InterruptedException e) { Thread.currentThread().interrupt(); return; }
		while (true) {
			try {
				if (!musicEnabled) { Thread.sleep(1000); continue; }
				String[] track = BYTEBEAT[nextTrack()];
				int rate = Integer.parseInt(track[2]);
				short[] samples = renderBytebeat(track, rate);
				musicVoice = new MusicVoice(samples, samples.length, rate);
				say("Now playing: " + track[0] + " by " + track[1]);
				while (musicVoice != null && !musicVoice.finished()) Thread.sleep(100);
				musicVoice = null;
				Thread.sleep(60000);
			} catch (Throwable e) {
				System.err.println("Bytebeat player error: " + e);
				e.printStackTrace();
				musicVoice = null;
				try { Thread.sleep(5000); } catch (InterruptedException ignored) { Thread.currentThread().interrupt(); return; }
			}
		}
	}

	static short[] renderBytebeat(String[] track, int rate) throws Exception {
		return renderBytebeatJava(track[0], rate * BB_MAX_SECONDS, rate);
	}

	static short[] renderBytebeatJava(String name, int count, int rate) {
		short[] out = new short[count];
		double[] rev = new double[12288]; int rp = 0; double[] delay = new double[120000];
		double[] echo = "echo_testing".equals(name) ? new double[12287] : null;
		double lg = .5;
		for (int i = 0; i < count; i++) {
			double t = i, v = 128;
			if ("e".equals(name)) {
				long ti = (long)t;
				double x0 = eWave(ti);
				double x1 = eWave(ti - (((ti >> 9) & 255)));
				double x2 = eWave(ti - 12288L);
				double x3 = eWave(ti - 24888L);
				double noise = RND.nextDouble() * ((-ti >> 7) & 63);
				v = (x0 / 4.0 + x1 / 4.0 + x2 / 8.0 + x3 / 8.0 + noise + 32.0 * Math.sin(3.0 * Math.sqrt(ti % 16384L))) / 3.0 + 64.0;
			} else if ("Useless1".equals(name)) {
				int[] notes={-8,-5,2,4,7,14,7,4,2,-5,-8,-5,2,4,7,14,-10,-6,1,2,6,13,6,2,1,-6,-10,-6,1,2,6,13};
				String melody="12132210", scale="34567777";
				int ni=((int)t >> 13) & 31;
				double pitch = t * 3.5 * Math.pow(2.0, notes[ni] / 12.0);
				int mi = ((int)(pitch / 32.0)) & 7;
				int si = (((int)t >> 10) & 7);
				double r = (melody.charAt(mi) - '0') / (double)(scale.charAt(si) - '0');
				r += rev[rp];
				rev[rp] = r / 2.0;
				rp = (rp + 1) % rev.length;
				v = r * 96.0;
			} else if ("qai".equals(name)) {
				double q=t/5000.0,k=(q/4)%1; int qi=(int)q; double c=(1+ ("7798".charAt((qi/16)&3)-'0'))/8.0;
				int ix=((int)t)%30000; double w1=Math.sin(Math.PI*Math.sin(t/2.7/(qi%4+(qi/4&3)+1)*c));
				double w2=Math.sin(Math.PI*Math.sin(t/2.7/(16.0/("11022122".charAt(qi&7)-'0'))*c));
				double ss=22*w1+28*Math.asin(Math.max(-1,Math.min(1,w2)))+delay[ix]; delay[ix]=ss/3+delay[(ix+15000)%delay.length]/4+delay[(ix+7500)%delay.length]/3;
				v=k*ss+28*Math.sin(20*Math.pow(Math.max(0,1000*k),.4)-1000*Math.pow(Math.max(0,1-k),(((int)(8*q))&32)))+128;
			} else if ("ÐiskΩtroÑ".equals(name)) {
				int ti=(int)t, digit="0032".charAt((ti>>10)&3)-'0';
				int cond=((ti>>10)-((ti>>14)&1)+((((~ti>>12)&1)^((ti>>13)&1))==0?1:0))&1;
				int shift=(cond!=0)?14:10;
				int inner=(ti & (digit*ti)) | (ti>>5) | ((ti*6)&(ti>>shift)) | ((ti&20)!=0?1:(5+((3*ti>>9)&31)));
				int raw=(inner-(ti>>5))&255;
				double cs=Math.cos(99*(3+(ti>>10&4))/Math.pow((ti%4096)+1,.1));
				v=raw/2.0+64+32*cs*cs+(((~ti>>(7-(((ti>>12)&3)==0?1:0)))&12)*Math.pow(Math.cos(t*t*t),2));
			} else if ("Steady On Tim, It's Only A Budget Game".equals(name)) {
				double T=t/5000.0; v=steady(T,t)/3+steady(T-3,t)/5;
				if (((int)T>>7)!=0) v += (((int)(t*Math.pow(2,(((int)T&4)!=0?((int)T&7)-1:0)/6.0-4))&63)*(197>>(int)T%8&1))+Math.random()*32*(1-(T+4)%8/8);
			} else if ("Crystal Cave".equals(name)) {
				v=(crystal(t)/1.5+crystal(t-3000)/2+crystal(t-6000)/3)+100;
			} else if (name.startsWith("Phantasie")) {
				double i2 = t / 32768.0 - 2;
				v = phR(1, 0, t, i2) + phR(2, 0, t, i2) + phR(2, 1, t, i2);
			} else if ("echo_testing".equals(name)) {
				int ti = (int) t;
				if (ti == 0) Arrays.fill(echo, 64);
				double q = ti * 8.0 / (4 + ((ti >> 15) & 3)) * (1 + ((ti >> 13) & 3));
				int c = (ti32(q) >> ((((ti >> 12) & 3) == 0) ? 1 : 0)) & 128;
				double x = (c * Math.pow(1.00009, (-ti) % 16384)) % 256 / 4.0;
				int k = ti % 12287;
				double cc = x % 256 + echo[k];
				echo[k] = cc * .8;
				v = cc * 2;
			} else if ("Random Bytebeat Loop Song".equals(name)) {
				int ti = (int) t;
				double p = t * Math.pow(1.125, RB_P.charAt((ti >> 15) & 15) - '0') / 8.0;
				double s = t * Math.pow(1.25, RB_S.charAt((ti >> 14) & 63) - '0') * (RB_G.charAt((ti >> 11) & 63) - '0') / 32.0;
				v = (ti32(p) & 16) + (ti32(1.02 * p) & 16) + (ti32(1.51 * p) & 16) + (ti32(1.53 * p) & 16)
					+ (16 * Math.sin(p / 3) + 16 * Math.cos(p / 4))
					+ s % 16 + (1.5 * s) % 16 + (s / 2) % 16 + (s / 2 * 1.5) % 16
					+ RND.nextDouble() * ((((-ti) >> 6) & 31) + 1) * (((-ti) >> 11) & 1)
					+ RND.nextDouble() * ((((-ti) >> 8) & 31) + 1) * (((-ti) >> 13) & 1) + 32;
			} else if ("arpeggiator fun".equals(name)) {
				double b = t / 441e3 * 16, q = b % .5;
				int s = (int) (b * 2) % 32, a = Math.abs(8 - (int) (b * 8) % 16);
				if (i == 0) lg = .5;
				lg = 3.65 * lg * (1 - lg);
				int lead = (s == 6 && (int) ((b * 6) % 6) == 1) ? 85 : (s == 14 && q < .25) ? 78 : ARP_LEAD.charAt(s);
				v = Math.sin(q / (q / 100 + 3e-4)) * 40 * (((54878 & (1 << (s % 16))) == 0) ? 1 : 0)
					+ (lg - .5) * 70 * Math.max(0, 1 - ((b + 1) % 2) * .77)
					+ arpW(t, b, lead, s == 5 ? 1 : 0)
					+ arpW(t, b, ARP_BASS.charAt(s), 0)
					+ arpH(t, ARP_ARP.charAt(a % 4 + (s / 8) * 4) + 12 * -(a / 4)) * 27 + 99;
			} else if ("Chase in the Forest".equals(name)) {
				double T = t / 5E3; int b = ti32(T) >> 7, k = ((b + 2) & 4) != 0 ? 4 : 8;
				double ch = chaseS(t, T, 2, 0, 0) + chaseS(t, T, 2, 0, 3) / 2;
				if (b != 0) ch += chaseS(t, T, 0, -2, 0);
				if (b > 1) ch += chaseS(t, T, 1, k / 4.0, 0) * (1 - T % 16 / 20);
				if (b > 2) ch += .4 * chaseN(T, 1E6) * (1 - (T + k / 2.0) % k / k);
				if (b > 3) {
					ch += ti32(64 / (T % k)) & 64;
					if ((ti32(T) & k) != 0) ch += .6 * chaseN(T, 330) * (1 - T % k / k);
				}
				v = ch;
			}
			out[i]=(short)Math.round(normalizeBytebeat(v)*32767f);
		}
		return out;
	}

	// Fast Java equivalent of x=t=>(1.22*t*1.0596**parseInt(...,36)&128)*(-t>>8&31)/16.
	// The source selects one of eight fixed characters; cache their base-36 powers instead of
	// parsing strings and exponentiating on every sample.
	static final double[] E_PITCH = { Math.pow(1.0596, 17), 1,
		Math.pow(1.0596, 12), Math.pow(1.0596, 10), Math.pow(1.0596, 17),
		1.0596, Math.pow(1.0596, 13), Math.pow(1.0596, 12) };

	static double eWave(long t) {
		int row = (int)(1L & (t >> 17));
		int col = (int)(3L & (t >> 13));
		int pitchIndex = row * 4 + col;
		int gate = ((int)(1.22 * t * E_PITCH[pitchIndex])) & 128;
		int envelope = (int)((-t >> 8) & 31);
		return gate * envelope / 16.0;
	}

	static double steady(double T, double t) {
		int ti=(int)T; double b=Math.abs((ti&31)-16);
		double K=1+((1-((ti>>5)&3))%2-1)/6.0;
		int[] notes={-1,4,7};
		int n=Math.floorMod((int)(T*4%3),3);
		double first=(int)(t*Math.pow(2,notes[n]/12.0+K))&128;
		first *= ((ti>>8)!=0?12-T%12:0)/12.0;
		int divisor=((ti>>9)!=0?4:5);
		int table=(5514 >> ((int)(b%divisor)*4))&15;
		double second=(int)(t*Math.pow(2,K+(int)(b/5)-table/12.0))&128;
		return first+second;
	}

	static double crystal(double t) {
		int ti=(int)t; double den=(((ti>>10&3)^(ti>>13&6)|(ti>>12&7))+2);
		return Math.cbrt(Math.cos(t/den))*(32-(ti>>6)&31)+32;
	}

	static int ti32(double x) { return (int) (long) x; } // JS ToInt32 (NaN -> 0)
	static double bbTri(double x) { return Math.abs(x % 2 - 1); }

	// --- Phantasie für drei Blockflöten ---
	static final String PH_NOTES = "66DAD0035655ACD";
	static double phS(int A, int B, int C, double i) {
		int idx = (A + 6 * (i > 58 - C ? 1 : 0)) * ((int) i | B) % 15;
		return idx < 0 ? Double.NaN : Character.digit(PH_NOTES.charAt(idx), 16); // JS: undefined -> NaN
	}
	static double phR(int A, int B, double t, double i) {
		int C = A + B;
		double d = phS(A, B, C, i + 1), V = bbTri(i * 4);
		double r1 = bbTri(t / 50 / C * Math.pow(1.06, d)) * 30 * C;
		double r2 = bbTri(t / 50 / C * Math.pow(1.06, d + .1)) * 30 * C;
		double gate = i / 9 > 6 - 3 * A + B ? 1 : 0;
		double same = d == phS(A, B, C, i) ? 1 : 0, same2 = d == phS(A, B, C, i + 2) ? 1 : 0;
		double m = Math.min(Math.max(Math.max(i % 1, same), .7 - bbTri(i * 8)), 8 - i % 1 * 8 + same2);
		return (r1 * V + r2 * (1 - V)) * gate * m;
	}

	// --- Random Bytebeat Loop Song ---
	static final String RB_P = "5533224412321423";
	static final String RB_S = "4323432343234323432343234323432365456545654565456545654565456545";
	static final String RB_G = "1010110010101100101011001010110010001010100010101000101010001010";

	// --- arpeggiator fun ---
	static final String ARP_LEAD = "SSSSSSSQOOONNOLJLLLLLNLJIIIGGGGG", ARP_BASS = "@@@@@@BCEEECCBCCEEEEECEEBBB@@@@@", ARP_ARP = "pnkgrnkipmigpnkg";
	static double arpH(double t, double x) { return (t / 2210.0 * Math.pow(2, (x - 36) / 12.0)) % 1; }
	static double arpW(double t, double b, double x, double y) { return (arpH(t, x) - Math.sin(y * 2 + b * Math.PI) / 8 > .5 ? 1 : 0) * 30; }

	// --- Chase in the Forest ---
	static double chaseS(double t, double T, int s, double p, double d) {
		int idx = (int) ((T - d) / s % 3); // s == 0 gives NaN -> 0, like JS |0
		if (idx < 0) return 0;               // JS: undefined -> NaN -> &128 == 0
		int dig = "023".charAt(idx) - '0';
		double e = p + dig / 12.0 + ((1 - ((ti32(T) >> 5) & 3)) % 2 + 1) / 4.0;
		return (ti32(t * Math.pow(2, e)) & 128) / 3.0;
	}
	static int chaseN(double T, double p) { return ti32(1E5 * Math.sin(ti32(T * p))) & 64; }

	static float normalizeBytebeat(double value) {
		if (Double.isNaN(value) || Double.isInfinite(value)) value = 128;
		value %= 256; if (value < 0) value += 256;
		return (float) ((value - 128) / 128.0);
	}

	private static void mixer() {
		try {
			AudioFormat fmt = new AudioFormat(RATE, 16, 1, true, false);
			SourceDataLine line = AudioSystem.getSourceDataLine(fmt);
			line.open(fmt, 2048);
			line.start();
			byte[] out = new byte[1024];
			float[] mix = new float[512];
			while (true) {
				Arrays.fill(mix, 0);
				synchronized (voices) {
					for (Iterator<Voice> it = voices.iterator(); it.hasNext();) {
						Voice v = it.next();
						int n = Math.min(512, v.s.length - v.p);
						for (int i = 0; i < n; i++)
							mix[i] += v.s[v.p + i] * v.v;
						if ((v.p += n) >= v.s.length)
							it.remove();
					}
				}
				MusicVoice mv = musicVoice;
				if (mv != null && musicEnabled) {
					for (int i = 0; i < 512; i++) {
						long p = mv.position;
						double sourcePos = p * (double) mv.rate / RATE;
						long phase = (long) Math.floor(sourcePos);
						long local = phase < mv.loopSamples ? phase : phase % mv.loopSamples;
						int at = (int) Math.min(mv.loopSamples - 1L, local);
						int next = at + 1 < mv.loopSamples ? at + 1 : 0;
						double frac = sourcePos - Math.floor(sourcePos);
						float sample = (float) ((mv.samples[at] * (1 - frac) + mv.samples[next] * frac) / 32768.0);
						long end = (long) mv.loopSamples + mv.extraLoop;
						double musicPos = p * (double) mv.rate / RATE;
						double fin = Math.min(1, musicPos / mv.fadeIn);
						double gain = fin * fin * (3 - 2 * fin); // smoothstep
						if (musicPos >= end - mv.fadeOut) gain *= Math.max(0, (end - musicPos) / (double) mv.fadeOut);
						mix[i] += sample * (float) (gain * 0.40 * musicVolume);
						mv.position++;
						if (mv.finished()) { musicVoice = null; break; }
					}
				}
				for (int i = 0; i < 512; i++) {
					int s = (int) (Math.max(-1, Math.min(1, mix[i])) * 32000);
					out[2 * i] = (byte) s;
					out[2 * i + 1] = (byte) (s >> 8);
				}
				line.write(out, 0, out.length); // blocks, which paces the loop
			}
		} catch (Exception e) {
			System.err.println("Nexus audio mixer could not open/play audio: " + e);
			e.printStackTrace();
			sound = false;
		}
	}

	static void play(float[] s, double vol) {
		if (vol * soundVolume < 0.01)
			return;
		synchronized (voices) {
			if (voices.size() < 24)
				voices.add(new Voice(s, (float) (vol * soundVolume)));
		}
	}

	private static double dist(long bx, long by, long bz) {
		double dx = (bx - x.getIntegerPart()) + (0.5 - x.getFractionalPart());
		double dy = (by - y.getIntegerPart()) + (0.5 - y.getFractionalPart());
		double dz = (bz - z.getIntegerPart()) + (0.5 - z.getFractionalPart());
		return Math.sqrt(dx * dx + dy * dy + dz * dz);
	}

	/** action: 0 break, 1 place, 2 step */
	static void block(byte id, int action, long bx, long by, long bz) {
		if (id == AIR || !sound)
			return;
		play(bank[(kind(id) * 3 + action) * VAR + RND.nextInt(VAR)], soundGain(id) * 2 * VOLUME[action] * 0.5 / (1 + dist(bx, by, bz) * 0.1));
	}

	static void boom(long bx, long by, long bz) {
		play(boom, 2 / (1 + dist(bx, by, bz) * 0.05));
	}

	static void step(byte below, double moved) {
		if (below == AIR)
			return;
		walked += moved;
		if (walked > 1.8) {
			walked = 0;
			block(below, 2, floorOf(x), floorOf(y) + 1, floorOf(z));
		}
	}

	/** Per-material loudness multiplier. */
	static double soundGain(byte id) {
		return kind(id) == 3 ? 2.0 : 1.0; // wood is louder
	}

	// ------------------------------------------------------------------ main loop

	private void run() {
		try {
			spawn();
			center();
			textures();
			init();
			startWorkers();
			long start = System.nanoTime();

			while (true) {
				long frameStart = System.nanoTime();
				if (toggleFullscreenRequested) {
					toggleFullscreenRequested = false;
					try {
						SwingUtilities.invokeAndWait(Nexus::toggleFullscreen);
					} catch (Exception e) {
						e.printStackTrace();
					}
				}
				boolean idle = computeIdle();
				if (idle != titleIdle) {
					titleIdle = idle;
					final String t = idle ? "Bitwise Nexus " + VERSION + " - Inactive!" : "Bitwise Nexus " + VERSION;
					SwingUtilities.invokeLater(() -> frame.setTitle(t));
				}
				if (idle) {
					try { Thread.sleep(200); } catch (InterruptedException e) { Thread.currentThread().interrupt(); }
				}
				Runnable task;
				while ((task = tasks.poll()) != null)
					task.run();

				long autosaveNow = System.currentTimeMillis();
				// The title-screen preview reuses the renderer/camera, but it is not a playable
				// world. Never let its forced preview coordinates overwrite a saved world.
				if (!mainMenu && persistentStorage && activeSaveFile != null && autosaveNow - lastPersistentSave >= 30_000L) {
					requestedSaveFile = activeSaveFile;
					saveRequested = true;
					lastPersistentSave = autosaveNow;
				}
				if (saveRequested && !saveInProgress.get()) {
					File requested = requestedSaveFile != null ? requestedSaveFile : activeSaveFile;
					if (requested != null) {
						saveRequested = false;
						doSave(requested);
					}
				}

				if (paused || dialogOpen) {
					// Keep menus/dialogs responsive while suspending simulation.
					sigValid = false;
					try { Thread.sleep(80); } catch (InterruptedException e) { Thread.currentThread().interrupt(); }
					continue;
				}

				if (mainMenu) {
				    // Render the title-screen preview at 30 FPS.
				    long nowNs = System.nanoTime();
				    if (nowNs - lastMenuFrameNs < 33_333_333L) {
				        try {
				            Thread.sleep(33);
				        } catch (InterruptedException e) {
				            Thread.currentThread().interrupt();
				        }
				        continue;
				    }

				    long elapsedNs = lastMenuFrameNs == 0L ? 0L : nowNs - lastMenuFrameNs;
				    lastMenuFrameNs = nowNs;

				    // Keep the title-screen preview airborne and fixed in place.
				    fly = true;
				    x.setValue(15493); y.setValue(96); z.setValue(17236);
				    velX = velY = velZ = 0;
				    pitch = -2.0 / 3.0;

				    double deltaSeconds = Math.min(elapsedNs / 1E9, 0.1);
				    yaw += 0.1 * deltaSeconds;
				}

				if (lock && focus && System.currentTimeMillis() - focusTime >= 200)
					lock = false;

				ensureChunks();
				cleanupOldChunks();
				// Hold the player completely still until the destination chunk has loaded
				// and had a brief settle period. This prevents gravity/movement from being
				// applied against partially loaded terrain immediately after world load.
				if (worldLoading) {
					velX = velY = velZ = 0;
					if (world.chunk(chunkOf(x), chunkOf(y), chunkOf(z)) != World.UNLOADED) {
						if (worldLoadReadyAt == 0L) worldLoadReadyAt = System.currentTimeMillis() + 300L;
						if (System.currentTimeMillis() >= worldLoadReadyAt) {
							worldLoading = false;
							worldLoadReadyAt = 0L;
							prevX.set(x); prevY.set(y); prevZ.set(z);
							velX = velY = velZ = 0;
						}
					} else worldLoadReadyAt = 0L;
				}
				// Do not serialize the entire world on the simulation thread. Persistent
				// chunks are retained in savedChunks as they unload and written on Save.
				if (needGround) {
					needGround = false;
					groundY(floorOf(x), floorOf(z), y);
					velX = velY = velZ = 0;
				}
				if (update) {
					update = false;
					update();
				}
				updateHotbar();
				handleKeys();

				if (pitch <= -Math.PI / 2)
					pitch = -Math.PI / 2;
				if (pitch >= Math.PI / 2)
					pitch = Math.PI / 2;

				sinYaw = Math.sin(yaw);
				cosYaw = Math.cos(yaw);
				sinPitch = Math.sin(pitch);
				cosPitch = Math.cos(pitch);
				light.y = Math.sin(-time / 6000.0);
				light.z = Math.cos(-time / 6000.0);
				if (light.y < 0) {
					Vec3.lerp(SUN_LOW, SUN_DAY, -light.y, sunColor);
					Vec3.lerp(AMB_LOW, AMB_DAY, -light.y, ambColor);
					Vec3.lerp(SKY_LOW, SKY_DAY, -light.y, skyColor);
				} else {
					Vec3.lerp(SUN_LOW, SUN_NIGHT, light.y, sunColor);
					Vec3.lerp(AMB_LOW, AMB_NIGHT, light.y, ambColor);
					Vec3.lerp(SKY_LOW, SKY_NIGHT, light.y, skyColor);
				}

				start = runTicks(start);
				updateView();
				updateCaveMix();

				final boolean reuse = sceneUnchanged();
				if (!reuse) {
					newHoverY = NO_POS;
					Render.prepare();
					renderFrame();
					Particles.render();
					hoveredX = newHoverX;
					hoveredY = newHoverY;
					hoveredZ = newHoverZ;
					dirX = newDirX;
					dirY = newDirY;
					dirZ = newDirZ;
					swapBuffers();
				}
				repaint();
				frames++;
				long frameTime = System.currentTimeMillis();
				if (frameTime - fpsTime >= 1000) {
					fps = frames;
					frames = 0;
					fpsTime = frameTime;
				}
				limitFrame(frameStart);
			}
		} catch (HeadlessException e) {
			e.printStackTrace();
		}
	}

	static boolean computeIdle() {
		long now = System.currentTimeMillis();
		if (mouseButtonsDown > 0) activity = now;
		if (mainMenu) {
			activity = now;
			return false;
		}
		return now - activity > 15000;
	}

	private void takeScreenshot() {
		try {
			Path dir = Paths.get("screenshots"); Files.createDirectories(dir);
			String stamp = new SimpleDateFormat("yyyyMMdd-HHmmss").format(new Date());
			Path file = dir.resolve("Nexus-" + stamp + ".png");
			BufferedImage shot = new BufferedImage(width, height, 1);
			Graphics2D sg = shot.createGraphics(); paint(sg); sg.dispose();
			ImageIO.write(shot, "png", file.toFile()); say("Screenshot saved: " + file);
		} catch (Exception ex) { say("Screenshot failed: " + ex.getMessage()); }
	}

	private static void updateHotbar() {
		byte[] want = survival ? invId[page % INV_PAGES] : (xor ? XOR_PAGE : PAGES[page]);
		if (hotbar != want)
			hotbar = want;
		if (heldBlock >= want.length || heldBlock < 0)
			heldBlock = 0;
	}

	private static void toggleDebugHud() {
		if (controlsUIEnabled) { controlsUIEnabled = false; option = 0; guiEnabled = true; } // F4 screen -> F3 goes straight to the debug HUD
		else guiEnabled = !guiEnabled;
	}

	private static void handleKeys() {
		if (fire(KeyEvent.VK_F1, 200)) hideEverything = !hideEverything;
		if (fire(KeyEvent.VK_F3, 200)) toggleDebugHud();
		if (fire(KeyEvent.VK_F4, 200)) { controlsUIEnabled = !controlsUIEnabled; option = (byte)(controlsUIEnabled ? 2 : 0); }
		if (key(KeyEvent.VK_T))
			yaw = pitch = 0;
		if ((survival || !xor) && fire(KeyEvent.VK_E, 200)) page = (page + 1) % pageCount();
		if ((survival || !xor) && fire(KeyEvent.VK_Q, 200)) page = (page + pageCount() - 1) % pageCount();

		boolean f5 = key(KeyEvent.VK_F5);
		if (f5) {
			if (fire(KeyEvent.VK_1, 200)) showFPS = !showFPS;
			if (fire(KeyEvent.VK_2, 200)) showXYZ = !showXYZ;
			if (fire(KeyEvent.VK_3, 200)) showRot = !showRot;
			if (fire(KeyEvent.VK_4, 200)) showCyan = !showCyan;
			if (fire(KeyEvent.VK_5, 200)) showMagenta = !showMagenta;
			if (fire(KeyEvent.VK_6, 200)) showExtra = !showExtra;
		} else {
			byte[] hb = hotbar;
			for (int i = 0; i < hb.length; i++) {
				if (key(KeyEvent.VK_1 + i)) { heldBlock = (byte) i; break; }
			}
		}

		if (fire(KeyEvent.VK_F6, 200)) vSync = !vSync;
		if (fire(KeyEvent.VK_F7, 500)) fill = true;
		if (fill && fire(KeyEvent.VK_C, 250)) copyMode = !copyMode;
		if (fire(KeyEvent.VK_F8, 500)) {
			fill = false;
			boolean all = x0 != NO_POS && y0 != NO_POS && z0 != NO_POS && x1 != NO_POS && y1 != NO_POS && z1 != NO_POS;
			if (all) {
				long ax = Math.min(x0, x1), ay = Math.min(y0, y1), az = Math.min(z0, z1);
				long bx = Math.max(x0, x1) + 1, by = Math.max(y0, y1) + 1, bz = Math.max(z0, z1) + 1;
				if (copyMode) copyRegion(ax, ay, az, bx, by, bz);
				else if (survival) fillFromInventory(hotbar[heldBlock], ax, ay, az, bx, by, bz);
				else fill(hotbar[heldBlock], ax, ay, az, bx, by, bz, true);
			}
			copyMode = false;
			x0 = y0 = z0 = x1 = y1 = z1 = NO_POS;
		}
		if (key(KeyEvent.VK_U)) showFPS = showXYZ = showRot = showCyan = showMagenta = showExtra = true;
		if (!survival && fire(KeyEvent.VK_F, 200)) fly = !fly;        // flight disabled in survival
		if (key(KeyEvent.VK_G)) outline();                            // guarded inside outline()
		if (!survival && fire(KeyEvent.VK_N, 250)) {
			locTarget = (locTarget + 1) % LOC_NAMES.length;
			say("Locate: " + LOC_NAMES[locTarget] + " (B to teleport)");
		}
		if (!survival && fire(KeyEvent.VK_B, 500)) locate(locTarget);
		if (fire(KeyEvent.VK_L, 250)) {
			lightQ = (lightQ + 1) % 3;
			say("Lighting: " + LIGHT_NAMES[lightQ]);
		}
	}

	// ---- persistent render threads (no per-frame futures) ----
	static void startWorkers() {
		for (final Render w : workers) {
			final Semaphore s = new Semaphore(0);
			w.go = s;
			Thread t = new Thread(() -> {
				while (true) {
					s.acquireUninterruptibly();
					try { w.call(); } catch (Throwable e) { e.printStackTrace(); }
					finally { finished.release(); }
				}
			}, "nexus-render-" + workers.indexOf(w));
			t.setDaemon(true);
			// Slightly favour the main loop and Swing EDT over background pixel work.
			t.setPriority(Thread.NORM_PRIORITY - 1);
			t.start();
		}
	}

	static void renderFrame() {
		// Do not wake more workers than there are tiles to render. At low detail or
		// small window sizes, waking the full pool only adds semaphore/context-switch
		// overhead and can steal time from the game loop.
		int active = Math.min(workers.size(), Math.max(1, Render.tilesTotal));
		for (int i = 0; i < active; i++) workers.get(i).go.release();
		finished.acquireUninterruptibly(active);
	}

	// ---- skip rendering when nothing visible changed ----
	private static long lastSig, lastSigTime;
	private static boolean sigValid;

	private static long sigMix(long h, long v) { h = (h ^ v) * 0x9E3779B97F4A7C15L; return h ^ (h >>> 31); }

	private static boolean sceneUnchanged() {
		if (Render.warmIncomplete || Particles.count != 0) { sigValid = false; return false; }
		long h = 7;
		h = sigMix(h, viewX.hashCode()); h = sigMix(h, viewY.hashCode()); h = sigMix(h, viewZ.hashCode());
		h = sigMix(h, Double.doubleToLongBits(yaw)); h = sigMix(h, Double.doubleToLongBits(pitch));
		h = sigMix(h, Double.doubleToLongBits(focal));
		h = sigMix(h, width * 65536L + height); h = sigMix(h, detail); h = sigMix(h, dist); h = sigMix(h, reach);
		h = sigMix(h, ((long) worldVer << 32) ^ streamVer);
		h = sigMix(h, lightQ | (classic ? 4 : 0) | (xor ? 8 : 0) | (lanternEnabled ? 16 : 0) | (display ? 32 : 0)
				| (hideEverything ? 64 : 0) | (caves ? 128 : 0) | (terrain3D ? 256 : 0) | (blockLightingEnabled ? 512 : 0));
		h = sigMix(h, Double.doubleToLongBits(AO_STRENGTH));
		h = sigMix(h, Double.doubleToLongBits(red)); h = sigMix(h, Double.doubleToLongBits(green)); h = sigMix(h, Double.doubleToLongBits(blue));
		h = sigMix(h, Math.round(caveMix * 1000));
		h = sigMix(h, breakStage + 1L); h = sigMix(h, breakX ^ (breakY * 31) ^ (breakZ * 131));
		boolean same = sigValid && h == lastSig && Math.abs(time - lastSigTime) < 25; // sun moves ~0.3° per 25 ticks
		if (!same) { lastSig = h; lastSigTime = time; sigValid = true; }
		return same;
	}

	// ------------------------------------------------------------------ physics

	private static void tick(long now) {
		if (worldLoading) {
			velX = velY = velZ = 0;
			return; // no gravity, input movement, or collision resolution during world load
		}
		if (!freezeTime) time++;
		if (survival) fly = false;
		double tau = Math.PI * 2;
		yaw = (yaw % tau + tau) % tau;
		if (sprintRequest) {
			sprintRequest = false;
			if (key(KeyEvent.VK_W))
				sprint = true;
		}
		if (!key(KeyEvent.VK_W))
			sprint = false;
		double speed = fly ? flight : (sprint ? 0.03 : 0.02);
		double inputX = (b2i(key(KeyEvent.VK_D)) - b2i(key(KeyEvent.VK_A))) * speed;
		double inputZ = (b2i(key(KeyEvent.VK_W)) - b2i(key(KeyEvent.VK_S))) * speed;
		if (inputX != 0 || inputZ != 0 || key(KeyEvent.VK_W) || key(KeyEvent.VK_S) || key(KeyEvent.VK_A) || key(KeyEvent.VK_D))
			activity = now;
		if (key(KeyEvent.VK_UP))
			pitch += 0.02;
		if (key(KeyEvent.VK_DOWN))
			pitch -= 0.02;
		if (key(KeyEvent.VK_LEFT))
			yaw -= 0.02;
		if (key(KeyEvent.VK_RIGHT))
			yaw += 0.02;
		if (pitch <= -Math.PI / 2)
			pitch = -Math.PI / 2;
		if (pitch >= Math.PI / 2)
			pitch = Math.PI / 2;

		if (world.chunk(chunkOf(x), chunkOf(y), chunkOf(z)) == World.UNLOADED) {
			velX = velY = velZ = 0; // wait for the chunk under to arrive
			return;
		}
		velX *= 0.5;
		velZ *= 0.5;
		velX += sinYaw * inputZ + cosYaw * inputX;
		velZ += cosYaw * inputZ - sinYaw * inputX;
		if (!fly) {
			velY += 0.003;
		} else {
			velY = 0;
			if (key(KeyEvent.VK_SHIFT))
				velY += flight;
			if (key(KeyEvent.VK_SPACE))
				velY -= flight;
		}

		byte below = getBlock(blockAt(x, 0), blockAt(y, 1.5), blockAt(z, 0));
		if (below == TOPAZ && velY <= 0)
			velY = -0.2;
		if (below == ICE) {
			velX *= 1.27;
			velZ *= 1.27;
		} else if (below == SAND) {
			velX *= 0.79;
			velZ *= 0.79;
		}

		final double vy0 = velY;
		final boolean wasStuck = collides();
		if (wasStuck) {
			// Embedded by something external (teleport, generation...): carve free, don't move.
			for (byte collider = 0; collider < 12; collider++) {
				long mx = blockAt(x, (collider & 1) * 0.6 - 0.3);
				long my = blockAt(y, ((collider >> 2) - 1) * 0.8 + 0.65);
				long mz = blockAt(z, (collider >> 1 & 1) * 0.6 - 0.3);
				setBlock(mx, my, mz, AIR);
			}
		} else {
			for (byte axis = 0; axis < 3; axis++) {
				final double dX = velX * ((axis + AXIS_Y) % 3 / 2);
				final double dY = velY * ((axis + AXIS_X) % 3 / 2);
				final double dZ = velZ * ((axis + AXIS_Z) % 3 / 2);
				if (dX == 0 && dY == 0 && dZ == 0)
					continue;
				BACK_X.set(x); BACK_Y.set(y); BACK_Z.set(z);
				shift(x, dX);
				shift(y, dY);
				shift(z, dZ);
				if (collides()) { // tested at the real new position, so no rounding mismatch
					x.set(BACK_X); y.set(BACK_Y); z.set(BACK_Z);
					if (axis != AXIS_Z)
						continue;
					if (key(KeyEvent.VK_SPACE) && velY > 0) {
						velY = -0.1;
						break;
					}
					velY = 0;
					break;
				}
			}
		}

		double dxMoved = diff(x, prevX), dzMoved = diff(z, prevZ);
		double moved = (dxMoved == 0.0 && dzMoved == 0.0) ? 0.0 : Math.hypot(dxMoved, dzMoved);
		step(fly ? AIR : below, moved);
		Particles.sprintTrail(fly ? AIR : below, moved);
		Particles.update();
		checkDamage(below, vy0, wasStuck);
	}

	private static final SplitDecimal BACK_X = new SplitDecimal(), BACK_Y = new SplitDecimal(), BACK_Z = new SplitDecimal(); // main thread only

	private static boolean intersectsPlayer(long bx, long by, long bz) {
		final boolean any = by == NO_POS;
		for (byte c = 0; c < 12; c++) {
			long mx = blockAt(x, (c & 1) * 0.6 - 0.3);
			long my = blockAt(y, ((c >> 2) - 1) * 0.8 + 0.65);
			long mz = blockAt(z, (c >> 1 & 1) * 0.6 - 0.3);
			if (any ? getBlock(mx, my, mz) != AIR : (mx == bx && my == by && mz == bz))
				return true;
		}
		return false;
	}

	private static boolean collides() {
		return intersectsPlayer(NO_POS, NO_POS, NO_POS);
	}

	// ------------------------------------------------------------------ world generation

	static void groundY(long bx, long bz, SplitDecimal out) {
		long cy0 = chunkOf(y);
		long yy = Math.max(topBound(), (cy0 - radius) * SIZE);
		long end = (cy0 + radius + 1) * SIZE;
		while (yy < end) {
			Octree c = world.chunk(bx >> SHIFT, yy >> SHIFT, bz >> SHIFT);
			if (c == World.UNLOADED)
				break;
			if (c == null) { // empty chunk: jump to its far side
				yy = ((yy >> SHIFT) + 1) << SHIFT;
				continue;
			}
			int f = c.find((int) (bx & MASK), (int) (yy & MASK), (int) (bz & MASK));
			if (f < 0) { // mixed 2x2x2 cell
				if (c.get((byte) (bx & MASK), (byte) (yy & MASK), (byte) (bz & MASK)) != AIR) {
					out.setValues(yy, -1.54);
					return;
				}
				yy++;
			} else if ((f & 0xFF) != AIR) {
				out.setValues(yy, -1.54);
				return;
			} else {
				yy = (yy | ((1L << (f >> 8)) - 1)) + 1; // skip the rest of this air cube
			}
		}
		out.setValue(estimateGround(bx, bz));
	}

	private static void spawn() {
		Random rand = new Random();
		int spawnX = rand.nextInt(65536) - 32768;
		int spawnZ = rand.nextInt(65536) - 32768;
		x.setValue(spawnX + 0.5);
		z.setValue(spawnZ + 0.5);
		groundY(floorOf(x), floorOf(z), y); // estimate; refined from real blocks once the chunks exist
		needGround = true;
		chunkDirty = true;
		worldSpawnX.set(x); worldSpawnY.set(y); worldSpawnZ.set(z);
	}

	static double estimateGround(long bx, long bz) {
		if (terrain3D) {
			double half = 0.5 * TK * Math.abs(amp) * TDIV;
			double lo = Math.floor(TBASE - half) - 1, hi = Math.ceil(TBASE + half) + 1;
			final int N = 4096;
			double prev = lo;
			for (int i = 0; i <= N; i++) {
				double yy = lo + (hi - lo) * i / N;
				if (density(bx, yy, bz) > 0) {
					double a = prev, b = yy;
					for (int k = 0; k < 64 && b - a > 1; k++) {
						double m = Math.floor(a + (b - a) / 2);
						if (m <= a) break;
						if (density(bx, m, bz) > 0) b = m; else a = m;
					}
					return b - 1.54;
				}
				prev = yy;
			}
			return TBASE - 1.54;
		}
		return terrainHeight(bx, bz) - 1.54;
	}

	static long terrainHeight(long wx, long wz) {
		return (long) ((Math.round(128 + noise(wx / 128.0, wz / 128.0) * amp * 50) - 1) * amp);
	}

	static long topBound() {
		if (terrain3D) {
			double half = 0.5 * TK * Math.abs(amp) * TDIV;
			return (long) Math.floor(TBASE - half) - 32; // margin for trees/spires/icicles
		}
		double a = 127 * amp, b = (127 + 100 * amp) * amp;
		return (long) Math.floor(Math.min(a, b)) - 32;
	}

	private static double noise(double x, double y) {
		long xi = (long) Math.floor(x);
		long yi = (long) Math.floor(y);
		double xd = x - xi;
		double yd = y - yi;
		double r = 0;
		for (int i = 0; i < 2; i++) {
			int of = (int) (((xi + (yi << 4)) % perlinRes + perlinRes) % perlinRes);
			double rx = (1 - Math.cos(xd * Math.PI)) * 0.5;
			double ry = (1 - Math.cos(yd * Math.PI)) * 0.5;
			double n1 = PERLIN[of];
			n1 += rx * (PERLIN[(of + 1) % perlinRes] - n1);
			double n2 = PERLIN[(of + 16) % perlinRes];
			n2 += rx * (PERLIN[(of + 17) % perlinRes] - n2);
			r += (n1 + ry * (n2 - n1));
			xi <<= 1;
			xd *= 2;
			yi <<= 1;
			yd *= 2;
			if (xd >= 1) { xi++; xd--; }
			if (yd >= 1) { yi++; yd--; }
		}
		return r;
	}

	private static double texNoise(double x, double y) {
		int xi = (int) Math.floor(x);
		int yi = (int) Math.floor(y);
		double xd = x - xi;
		double yd = y - yi;
		double r = 0;
		double a = 0.5;
		for (int i = 0; i < 4; i++) {
			int of = xi + (yi << 4);
			double rx = (1 - Math.cos(xd * Math.PI)) * 0.5;
			double ry = (1 - Math.cos(yd * Math.PI)) * 0.5;
			int wrapped = Math.floorMod(of, perlinRes);
			double n1 = PERLIN[wrapped];
			double n2 = PERLIN[Math.floorMod(wrapped + 1, perlinRes)];
			double n3 = PERLIN[Math.floorMod(wrapped + 16, perlinRes)];
			double n4 = PERLIN[Math.floorMod(wrapped + 17, perlinRes)];
			n1 += rx * (n2 - n1);
			n3 += rx * (n4 - n3);
			r += (n1 + ry * (n3 - n1)) * a;
			a *= 0.5;
			xi <<= 1;
			xd *= 2;
			yi <<= 1;
			yd *= 2;
			if (xd >= 1) {
				xi++;
				xd -= 1;
			}
			if (yd >= 1) {
				yi++;
				yd -= 1;
			}
		}
		return r;
	}

	/** Wraps a chunk-coordinate difference into the signed 21-bit range the chunk keys use. */
	static long wrap21(long d) {
		return (d << 43) >> 43;
	}

	private static boolean featureNeighboursReady(long cx, long cy, long cz) {
	    for (byte dx = -1; dx <= 1; dx++)
	        for (byte dy = -1; dy <= 1; dy++)
	            for (byte dz = -1; dz <= 1; dz++)
	                if (!world.has(cx + dx, cy + dy, cz + dz)) return false;
	    return true;
	}

	private static void runFeatureQueue() {
	    if (featureEpoch != world.epoch) {
	        featureQueue.clear();
	        featureEpoch = world.epoch;
	        return;
	    }
	    long end = System.nanoTime() + FEATURE_BUDGET_NS;
	    int scan = Math.min(featureQueue.size(), 256); // entries that must keep waiting rotate to the back
	    generating = true;
	    try {
	        while (scan-- > 0) {
	            long[] m = featureQueue.poll();
	            if (m == null) break;
	            if (!world.has(m[0], m[1], m[2])) continue; // unloaded while waiting; a reload queues it again
	            if (!featureNeighboursReady(m[0], m[1], m[2])) { featureQueue.add(m); continue; }
	            homeKey = World.key(m[0], m[1], m[2]);
	            features(m[0], m[1], m[2]);
	            autumnForestFeatures(m[0], m[1], m[2]);
	            caveFeatures(m[0], m[1], m[2]);
	            basinFeatures(m[0], m[1], m[2]);
	            mengerSpongeFeatures(m[0], m[1], m[2]);
	            // Replay cross-chunk feature writes immediately for already-loaded neighbors;
	            // otherwise tree canopies and other features can be clipped at chunk borders.
	            for (long dx = -1; dx <= 1; dx++) for (long dy = -1; dy <= 1; dy++) for (long dz = -1; dz <= 1; dz++) {
	                long nx = m[0] + dx, ny = m[1] + dy, nz = m[2] + dz;
	                if (world.has(nx, ny, nz)) applyPending(nx, ny, nz);
	            }
	            if (System.nanoTime() >= end) break;
	        }
	    } finally {
	        generating = false;
	        homeKey = World.NONE;
	    }
	}

	private static void cleanupOldChunks() { cleanupOldChunks(false); }

	/** force = skip the 1 s throttle and the 10 s grace period (used right after a teleport). */
	static void cleanupOldChunks(boolean force) {
	    long now = System.currentTimeMillis();
	    if (!force && now - lastChunkCleanup < 1000L) return;
	    lastChunkCleanup = now;
	    long cx = chunkOf(x), cy = chunkOf(y), cz = chunkOf(z);
	    long r2 = (long) radius * radius, cutoff = force ? Long.MAX_VALUE : now - 10000;
	    for (int s = 0; s < world.keys.length; s++) {
	        long k = world.keys[s];
	        if (k == World.NONE || world.seen[s] >= cutoff) continue;
	        long dx = wrap21(World.unpackX(k) - cx), dy = wrap21(World.unpackY(k) - cy), dz = wrap21(World.unpackZ(k) - cz);
	        if (dx * dx + dy * dy + dz * dz > r2)
	            unloadSlot(s);
	    }
	    prunePending(cx, cy, cz, force);
	    evictCache();
	}

	static long lastPrune;
	/** Feature writes aimed at chunks far from the player can never be needed again: drop them. */
	private static void prunePending(long cx, long cy, long cz, boolean force) {
	    long now = System.currentTimeMillis();
	    if (!force && now - lastPrune < 5000L) return;
	    lastPrune = now;
	    long lim = (long) (radius + 2) * (radius + 2);
	    Iterator<Map.Entry<Long, LinkedHashSet<Long>>> it = pendingWrites.entrySet().iterator();
	    while (it.hasNext()) {
	        Map.Entry<Long, LinkedHashSet<Long>> e = it.next();
	        long k = e.getKey();
	        long dx = wrap21(World.unpackX(k) - cx), dy = wrap21(World.unpackY(k) - cy), dz = wrap21(World.unpackZ(k) - cz);
	        if (dx * dx + dy * dy + dz * dz > lim) { pendingCount -= e.getValue().size(); it.remove(); }
	    }
	}

	private static boolean collectBatch() {
		GenBatch b = inFlight;
		for (Future<Octree> f : b.futures)
			if (!f.isDone())
				return false;
		inFlight = null;
		chunkDirty = true;
		if (b.epoch != world.epoch)
			return true;
		if (featureEpoch != world.epoch) {
			featureQueue.clear();
			featureEpoch = world.epoch;
		}
		long pcx = chunkOf(x), pcy = chunkOf(y), pcz = chunkOf(z), r2 = (long) radius * radius;
		for (int i = 0; i < b.coords.length; i++) {
			long[] m = b.coords[i];
			long dx = m[0] - pcx, dy = m[1] - pcy, dz = m[2] - pcz;
			if (dx * dx + dy * dy + dz * dz > r2)
				continue;
			Octree d = null;
			try {
				d = b.futures.get(i).get();
			} catch (Exception e) {
				e.printStackTrace();
			}
			int slot = world.slot(m[0], m[1], m[2]);
			unloadSlot(slot);
			world.put(m[0], m[1], m[2], d);
			if (d != null) userTopY = Math.min(userTopY, m[1] * SIZE);
			if (b.cachedRestore[i]) world.dirty[slot] = true;
			if (b.runFeatures[i]) applyPending(m[0], m[1], m[2]);
			if (b.runFeatures[i]) featureQueue.add(m);
		}
		return true;
	}

	/** Chunk offsets inside the load sphere, nearest first, packed as three biased bytes. */
	private static int[] loadOrder(int r) {
		if (r == loadOrderR)
			return loadOrder;
		int side = 2 * r + 1;
		long[] tmp = new long[side * side * side];
		int c = 0;
		for (int dx = -r; dx <= r; dx++)
			for (int dy = -r; dy <= r; dy++)
				for (int dz = -r; dz <= r; dz++) {
					int d2 = dx * dx + dy * dy + dz * dz;
					if (d2 > r * r)
						continue;
					tmp[c++] = (long) d2 << 24 | ((dx + 128) | (dy + 128) << 8 | (dz + 128) << 16);
				}
		Arrays.sort(tmp, 0, c);
		int[] o = new int[c];
		for (int i = 0; i < c; i++)
			o[i] = (int) (tmp[i] & 0xFFFFFF);
		loadOrderR = r;
		return loadOrder = o;
	}

	/** Moves the n smallest of a[0..m) to a[0..n), sorted ascending. */
	static void selectSmallest(long[] a, int m, int n) {
	    if (n >= m) { Arrays.sort(a, 0, m); return; }
	    Arrays.sort(a, 0, n);
	    long max = a[n - 1];
	    for (int i = n; i < m; i++) {
	        long v = a[i];
	        if (v >= max) continue;
	        int j = n - 1;
	        while (j > 0 && a[j - 1] > v) { a[j] = a[j - 1]; j--; }
	        a[j] = v;
	        max = a[n - 1];
	    }
	}

	private static void ensureChunks() {
		runFeatureQueue();
		if (inFlight != null && !collectBatch())
			return;

		long cx = chunkOf(x), cy = chunkOf(y), cz = chunkOf(z);
		int er = effectiveRadius();
		if (!chunkDirty && cx == lcx && cy == lcy && cz == lcz && er == lastLoadRadius)
			return;
		chunkDirty = false;
		lcx = cx; lcy = cy; lcz = cz;
		lastLoadRadius = er;

		int[] order = loadOrder(er);
		if (CAND.length < order.length) CAND = new long[order.length];
		final long[] cand = CAND;
		final double fx = cosPitch * sinYaw, fy = -sinPitch, fz = cosPitch * cosYaw; // look direction
		int m = 0;
		for (int i = 0; i < order.length; i++) {
			int o = order[i];
			int dx = (o & 255) - 128, dy = ((o >> 8) & 255) - 128, dz = ((o >> 16) & 255) - 128;
			if (world.has(cx + dx, cy + dy, cz + dz))
				continue;
			double d2 = dx * dx + dy * dy + dz * dz, len = Math.sqrt(d2);
			double facing = len == 0 ? 1 : (dx * fx + dy * fy + dz * fz) / len; // 1 ahead, -1 behind
			cand[m++] = (long) ((d2 + 6.0 * (1 - facing)) * 16) << 24 | o;      // chunks behind you wait
		}
		selectSmallest(cand, m, Math.min(m, MAX_LOAD_PER_PASS));
		int[] picked = new int[MAX_LOAD_PER_PASS];
		int n = Math.min(m, MAX_LOAD_PER_PASS);
		if (m > n)
			chunkDirty = true;
		for (int i = 0; i < n; i++)
			picked[i] = (int) (cand[i] & 0xFFFFFF);
		if (n == 0)
			return;

		long[][] coords = new long[n][];
		List<Future<Octree>> futures = new ArrayList<>(n);
		boolean[] featurePass = new boolean[n], cacheRestore = new boolean[n];
		for (int i = 0; i < n; i++) {
			int o = picked[i];
			long qx = cx + (o & 255) - 128, qy = cy + ((o >> 8) & 255) - 128, qz = cz + ((o >> 16) & 255) - 128;
			long key = World.key(qx, qy, qz);
			Object saved = savedChunks.get(key);
			boolean cached = false;
			if (saved == null && (saved = chunkCache.remove(key)) != null) {
				cacheBytes -= sizeOf(saved);
				cached = true;
			}
			final Object restoreValue = saved;
			final long[] coord = { qx, qy, qz };
			coords[i] = coord;
			if (restoreValue != null) {
				futures.add(genPool.submit(() -> restore(restoreValue)));
				cacheRestore[i] = cached;
			} else {
				futures.add(genPool.submit(() -> generate(coord[0], coord[1], coord[2])));
				featurePass[i] = true;
			}
		}
		inFlight = new GenBatch(coords, futures, featurePass, cacheRestore, world.epoch);
	}

	static final double TBASE = 160, TDIV = 24, TK = 10;

	static double plainsAt(double wx, double wz) {
		return smoothstep(0.58, 0.82, noise3(wx / 800.0, 0, wz / 800.0, 0x71));
	}

	static double density(double wx, double wy, double wz) {
		return density(wx, wy, wz, plainsAt(wx, wz));
	}

	static double density(double wx, double wy, double wz, double plains) {
		double rough = 0, flat = 0;
		if (plains < 1.0)
			rough = 0.50 * noise3(wx / 180.0, wy / 150.0, wz / 180.0, 0x11)
				  + 0.30 * noise3(wx / 64.0,  wy / 56.0,  wz / 64.0,  0x22)
				  + 0.20 * noise3(wx / 24.0,  wy / 28.0,  wz / 24.0,  0x33);
		if (plains > 0.0)
			flat = 0.5 + 0.055 * noise3(wx / 300.0, wy / 240.0, wz / 300.0, 0x91);
		double terrainNoise = rough * (1.0 - plains) + flat * plains;
		return (wy - TBASE) / TDIV + TK * amp * (terrainNoise - 0.5);
	}

	static double smoothstep(double edge0, double edge1, double x) {
		double t = (x - edge0) / (edge1 - edge0);
		t = Math.max(0.0, Math.min(1.0, t));
		return t * t * (3.0 - 2.0 * t);
	}

	private static Octree generate(long cx, long cy, long cz) {
		byte[] data = terrain3D ? generate3D(cx, cy, cz) : generate2D(cx, cy, cz);
		if (data == null)
			return null;
		if (caves) {
			carveCaves(data, cx, cy, cz);
			carveBasins(data, cx, cy, cz);
		}
		placeOres(data, cx, cy, cz);
		return Octree.build(data);
	}

	/**
	 * 3D terrain. Density is sampled on a 4-block lattice (extended 8 blocks above the chunk so surface depth is
	 * known at the top edge) and interpolated, so a chunk costs ~5.5k noise evaluations instead of 262k.
	 * A voxel with air above it is the surface block, the next 4 are the sub-surface, then stone/slate/magma by depth.
	 */
	private static byte[] generate3D(long cx, long cy, long cz) {
		boolean layerSet = false;
		double b1 = 0, b2 = 0;
		long baseX = cx * SIZE, baseY = cy * SIZE, baseZ = cz * SIZE;
		double half = 0.5 * TK * Math.abs(amp) * TDIV;
		if (baseY + SIZE - 1 < TBASE - half)
			return null; // entirely above the highest possible terrain
		final int n = CAVE_N, ny = n + 2, nyn = ny * n;
		float[] g = GEN_G.get();
		if (baseY - 8 >= TBASE + half) {
			byte u = uniformLayer(baseY - TBASE, baseY + SIZE - 1 - TBASE);
			if (u != AIR) {
				byte[] solid = denseBuf();
				Arrays.fill(solid, u);
				return solid;
			}
			Arrays.fill(g, 1f);
		} else {
			for (int gz = 0; gz < n; gz++)
				for (int gx = 0; gx < n; gx++) {
					double wx = baseX + gx * CAVE_STEP, wz = baseZ + gz * CAVE_STEP;
					double plains = plainsAt(wx, wz);
					for (int gy = 0; gy < ny; gy++)
						g[gz * nyn + gy * n + gx] = (float) density(wx, baseY - 8 + gy * CAVE_STEP, wz, plains);
				}
		}
		byte[] data = null;
		float[] col = GEN_COL.get();
		for (byte lz = 0; lz < SIZE; lz++) {
			int kz = lz >> 2;
			float fz = (lz & 3) * 0.25f;
			long wz = baseZ + lz;
			for (byte lx = 0; lx < SIZE; lx++) {
				int kx = lx >> 2;
				float fx = (lx & 3) * 0.25f;
				int base = kz * nyn + kx;
				boolean any = false;
				for (byte gy = 0; gy < ny; gy++) {
					int i = base + gy * n;
					float a = g[i] + fx * (g[i + 1] - g[i]);
					float b = g[i + nyn] + fx * (g[i + nyn + 1] - g[i + nyn]);
					col[gy] = a + fz * (b - a);
					if (col[gy] > 0) any = true;
				}
				if (!any)
					continue;
				layerSet = false; // layer1/layer2 depend on (x, z), so recompute for every column
				boolean biomeSet = false;
				byte top = GRASS, sub = DIRT;
				int run = 0; // solid voxels since the last air voxel above
				for (byte ly = -8; ly < SIZE; ly++) {
					int t = ly + 8, cell = t >> 2;
					float d = col[cell] + (t & 3) * 0.25f * (col[cell + 1] - col[cell]);
					if (d <= 0) {
						run = 0;
						continue;
					}
					run++;
					if (ly < 0)
						continue;
					byte block;
					if (run <= 5) {
						if (!biomeSet) {
							biomeSet = true;
							double val = noise((baseX + lx) / 512.0, wz / 512.0);
							if (val < 0.65) top = sub = SAND;
							else if (val > 1.4 && val < 1.85) top = sub = SNOW;
							else if (val > 1.85) top = sub = ICE;
							else if (isAutumnForest(baseX + lx, wz, val)) top = AUTUMN_GRASS;
						}
						block = run == 1 ? top : sub;
					} else {
						if (!layerSet) {
							layerSet = true;
							b1 = layer1(baseX + lx, wz);
							b2 = layer2(baseX + lx, wz);
						}
						block = layerBlock(baseY + ly - TBASE, b1, b2, (int) (baseX + lx), (int) (baseY + ly), (int) wz);
					}
					if (data == null)
						data = denseBuf();
					data[lx | (ly << SHIFT) | (lz << 2 * SHIFT)] = block;
				}
			}
		}
		return data;
	}

	/** Old 2D heightmap terrain. */
	private static byte[] generate2D(long cx, long cy, long cz) {
		byte[] data = null;
		long baseX = cx * SIZE, baseY = cy * SIZE, baseZ = cz * SIZE;
		for (int lz = 0; lz < SIZE; lz++) {
			long wz = baseZ + lz;
			for (int lx = 0; lx < SIZE; lx++) {
				long wx = baseX + lx;
				long terrainY;
				byte top, sub;
				double val = noise(wx / 512.0, wz / 512.0);
				terrainY = terrainHeight(wx, wz);
				if (val < 0.65) {
					top = sub = SAND;
				} else if (val > 1.4 && val < 1.85) {
					top = sub = SNOW;
				} else if (val > 1.85) {
					top = sub = ICE;
				} else if (isAutumnForest(wx, wz, val)) {
					top = AUTUMN_GRASS;
					sub = DIRT;
				} else {
					top = GRASS;
					sub = DIRT;
				}
				long first = Math.max(0, terrainY - baseY);
				if (first >= SIZE)
					continue;
				for (int ly = (int) first; ly < SIZE; ly++) {
					double b1 = layer1(wx, wz), b2 = layer2(wx, wz);
					long depth = baseY + ly - terrainY;
					byte block;
					if (depth == 0) block = top;
					else if (depth <= 4) block = sub;
					else block = layerBlock(depth, b1, b2, (int) wx, (int) (baseY + ly), (int) wz);
					if (data == null)
						data = denseBuf();
					data[lx | (ly << SHIFT) | (lz << 2 * SHIFT)] = block;
				}
			}
		}
		return data;
	}

	// ---- 3D value noise (hash based, works for any coordinate) ----

	private static double hash3(int x, int y, int z, int seed) {
		int h = x * 374761393 + y * 668265263 + z * 1274126177 + seed * 362437;
		h = (h ^ (h >>> 13)) * 1274126177;
		h ^= h >>> 16;
		return (h & 0xFFFFFF) * (1.0 / 0x1000000);
	}

	/** Smooth 3D value noise in [0, 1). */
	static double noise3(double x, double y, double z, int seed) {
		int xi = (int) (long) Math.floor(x), yi = (int) (long) Math.floor(y), zi = (int) (long) Math.floor(z);
		double xf = x - xi, yf = y - yi, zf = z - zi;
		xf = xf * xf * (3 - 2 * xf);
		yf = yf * yf * (3 - 2 * yf);
		zf = zf * zf * (3 - 2 * zf);
		double c000 = hash3(xi, yi, zi, seed), c100 = hash3(xi + 1, yi, zi, seed);
		double c010 = hash3(xi, yi + 1, zi, seed), c110 = hash3(xi + 1, yi + 1, zi, seed);
		double c001 = hash3(xi, yi, zi + 1, seed), c101 = hash3(xi + 1, yi, zi + 1, seed);
		double c011 = hash3(xi, yi + 1, zi + 1, seed), c111 = hash3(xi + 1, yi + 1, zi + 1, seed);
		double x00 = c000 + xf * (c100 - c000), x10 = c010 + xf * (c110 - c010);
		double x01 = c001 + xf * (c101 - c001), x11 = c011 + xf * (c111 - c011);
		double y0 = x00 + yf * (x10 - x00), y1 = x01 + yf * (x11 - x01);
		return y0 + zf * (y1 - y0);
	}

	// Cave tuning
	static final int CAVE_STEP = 4, CAVE_N = SIZE / CAVE_STEP + 1;
	static final double CAVE_W = 0.18, CAVE_XZ = 1 / 40.0, CAVE_Y = 1 / 56.0;
	private static final double CAVE_SURFACE_Y = 160;
	private static final double CAVE_FULL_DENSITY_Y = 1000;
	private static final double CAVE_SURFACE_WIDTH = 0.05;
	private static final ThreadLocal<float[]> GEN_G = ThreadLocal.withInitial(() -> new float[CAVE_N * (CAVE_N + 2) * CAVE_N]);
	private static final ThreadLocal<float[]> GEN_COL = ThreadLocal.withInitial(() -> new float[CAVE_N + 2]);
	private static final ThreadLocal<float[][]> CAVE_G = ThreadLocal.withInitial(() -> new float[2][CAVE_N * CAVE_N * CAVE_N]);
	private static final double MOSS_Y0 = 192, MOSS_Y1 = 256, MOSS_Y2 = 512, MOSS_Y3 = 768, MOSS_K = 2;
	private static final byte[] ORES        = { COAL_ORE, COPPER_ORE, IRON_ORE, GRAVEL, COAL, COPPER, IRON, RUBY, SAPPHIRE, AMETHYST, EMERALD, GOLD, GOLD_ORE, DIAMOND, TANZANITE, RHODONITE, QUARTZ };
	private static final byte[] ORE_HOST    = { STONE, STONE, STONE, STONE, SLATE, SLATE, SLATE, MAGMA, MAGMA, MAGMA, MOSS, SLATE, STONE, MAGMA, MAGMA, MAGMA, MAGMA };
	private static final int[] ORE_PERCENT  = { 70, 45, 40, 25, 10, 6, 6, 2, 2, 2, 5, 5, 10, 4, 3, 3, 4 }; // chance per 16^3 cell
	private static final double[] ORE_R_MIN = { 1.5, 1.5, 1.5, 2.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 0.8, 1.0, 1.0, 0.8 };
	private static final double[] ORE_R_MAX = { 3.0, 2.5, 2.5, 2.5, 2.0, 1.8, 1.8, 1.6, 1.6, 1.6, 1.0, 1.8, 1.8, 1.4, 1.6, 1.6, 1.4 }; // keep <= 3 (see PAD)
	private static final double LAYER1 = 128, LAYER2 = 1024, LAYER_BLEND = 8;
	// layer1 / layer2 never leave these ranges (see layer1 and layer2)
	private static final double L1_MIN = LAYER1 - 60, L1_MAX = LAYER1 + 60, L2_MIN = LAYER2 - 250, L2_MAX = LAYER2 + 250;

	private static byte uniformLayer(double depTop, double depBot) {
		if (depBot <= L1_MIN - LAYER_BLEND) return STONE;
		if (depTop >= L1_MAX + LAYER_BLEND && depBot <= L2_MIN - LAYER_BLEND) return SLATE;
		if (depTop >= L2_MAX + LAYER_BLEND) return MAGMA;
		return AIR; // crosses a (ragged) boundary: do it voxel by voxel
	}

	// Cave biomes (moss already existed; the other three are new)
	static final int CB_NONE = 0, CB_MOSS = 1, CB_SNOW = 2, CB_OBSIDIAN = 3, CB_CRYSTAL = 4, CB_BASALT = 5;
	private static final int[] CB_ORDER = { CB_CRYSTAL, CB_OBSIDIAN, CB_BASALT, CB_SNOW, CB_MOSS }; // priority
	private static final byte[] CB_BLOCK = { AIR, MOSS, SNOW, OBSIDIAN, ASH, BASALT };
	static final double BASIN_MAX_Y = 700, CRYSTAL_MAX_Y = 5000, OBSIDIAN_MAX_Y = 10000, BASALT_MAX_Y = 20000;

	private static double mossBand(double y) {
		return smoothstep(MOSS_Y0, MOSS_Y1, y) * (1 - smoothstep(MOSS_Y2, MOSS_Y3, y));
	}

	private static boolean inMagma(double wx, double y, double wz) {
		return y - TBASE > layer2(wx, wz) + LAYER_BLEND;
	}

	/** Hard on/off zone: no smoothstep, so edges are sharp. Magma layer only, and never deeper than maxY. */
	private static double hardZone(double wx, double cy, double wz, int seed, double scale, double threshold, double maxY) {
		if (cy > maxY || !inMagma(wx, cy, wz))
			return 0;
		// Fade biome edges instead of switching abruptly between 0 and 1.
		// This gives obsidian/crystal boundaries the same soft transition as moss/snow.
		double n = noise3(wx / scale, cy / (scale * 0.6), wz / scale, seed);
		return smoothstep(threshold - 0.06, threshold + 0.06, n);
	}

	/** 0 = not in this biome, up to 1 = fully inside. wx/wz are cell origins, cy the cell centre. */
	private static double zoneWeight(int biome, double wx, double cy, double wz) {
		switch (biome) {
		case CB_MOSS: {
			double band = mossBand(cy);
			return band <= 0 ? 0 : band * smoothstep(0.6, 0.78, noise3(wx / 220.0, cy / 90.0, wz / 220.0, 0x4D));
		}
		case CB_SNOW: {
			double band = mossBand(cy); // same Y range as moss
			if (band <= 0) return 0;
			// Feather the snow-biome edge so fog does not pop at the 1.4 threshold.
			double snowRegion = smoothstep(1.36, 1.44, noise(wx / 512.0, wz / 512.0));
			return band * snowRegion * smoothstep(0.5, 0.7, noise3(wx / 160.0, cy / 90.0, wz / 160.0, 0x4E));
		}
		case CB_OBSIDIAN: return hardZone(wx, cy, wz, 0x4F, 80.0, 0.78, OBSIDIAN_MAX_Y); // rarer
		case CB_CRYSTAL:  return hardZone(wx, cy, wz, 0x50, 120.0, 0.76, CRYSTAL_MAX_Y); // rarer
		case CB_BASALT:  return hardZone(wx, cy, wz, 0x51, 96.0, 0.84, BASALT_MAX_Y); // very rare magma caves
		}
		return 0;
	}

	/** Fog biome weight sampled at voxel centres, not the coarser cave-carving grid.
	 * Keeping the noise continuous here avoids visible 4x4x4 "sections" in fog.
	 */
	private static double zoneAt(int biome, long x, long y, long z) {
		return zoneWeight(biome, x + 0.5, y + 0.5, z + 0.5);
	}

	private static boolean replaceable(int biome, byte cur) {
		if (biome >= CB_OBSIDIAN)
			return cur == MAGMA; // obsidian/crystal only ever replace magma
		return cur == STONE || cur == SLATE || cur == DIRT; // never the surface biome layer
	}

	/** Stone/slate boundary depth for this column. */
	private static double layer1(double wx, double wz) {
		return LAYER1 + (noise3(wx / 70.0, 0, wz / 70.0, 0x5A) - 0.5) * 96 + (noise3(wx / 20.0, 0, wz / 20.0, 0x5C) - 0.5) * 24;
	}

	/** Slate/magma boundary depth for this column. */
	private static double layer2(double wx, double wz) {
		return LAYER2 + (noise3(wx / 200.0, 0, wz / 200.0, 0x5B) - 0.5) * 500;
	}

	private static byte layerBlock(double dep, double b1, double b2, int wx, int wy, int wz) {
		double d1 = dep - b1;
		if (d1 <= -LAYER_BLEND)
			return STONE;
		if (d1 < LAYER_BLEND) // ragged stone/slate edge
			return hash3(wx, wy, wz, 0x71A) < (d1 + LAYER_BLEND) / (2 * LAYER_BLEND) ? SLATE : STONE;
		double d2 = dep - b2;
		if (d2 <= -LAYER_BLEND)
			return SLATE;
		if (d2 < LAYER_BLEND) // ragged slate/magma edge
			return hash3(wx, wy, wz, 0x71B) < (d2 + LAYER_BLEND) / (2 * LAYER_BLEND) ? MAGMA : SLATE;
		return MAGMA;
	}

	private static double tri(float[] g, int i, int n, double fx, double fy, double fz) {
		int nn = n * n;
		double c00 = g[i] + fx * (g[i + 1] - g[i]);
		double c10 = g[i + n] + fx * (g[i + n + 1] - g[i + n]);
		double c01 = g[i + nn] + fx * (g[i + nn + 1] - g[i + nn]);
		double c11 = g[i + nn + n] + fx * (g[i + nn + n + 1] - g[i + nn + n]);
		double c0 = c00 + fy * (c10 - c00), c1 = c01 + fy * (c11 - c01);
		return c0 + fz * (c1 - c0);
	}

	private static boolean isMossZone(long wx, long wy, long wz) {
	    long step = CAVE_STEP;

	    long cellX = Math.floorDiv(wx, step) * step;
	    long cellY0 = Math.floorDiv(wy, step) * step;
	    long cellZ = Math.floorDiv(wz, step) * step;

	    double cellY = cellY0 + step / 2.0;

	    double band = smoothstep(MOSS_Y0, MOSS_Y1, cellY) * (1.0 - smoothstep(MOSS_Y2, MOSS_Y3, cellY));

	    if (band <= 0.0) {
	        return false;
	    }

	    double cellMoss = band * smoothstep(0.6, 0.78, noise3(cellX / 220.0, cellY / 90.0, cellZ / 220.0, 0x4D));

	    return cellMoss > 0.1 + 0.4 * hash3((int) wx, (int) wy, (int) wz, 0x4D);
	}

	private static void placeOres(byte[] data, long cx, long cy, long cz) {
		final long baseX = cx * SIZE, baseY = cy * SIZE, baseZ = cz * SIZE;
		// Skip ore families whose host block does not occur in this chunk.
		// This one linear scan can avoid all blob work in empty/upper chunks.
		boolean[] hostPresent = new boolean[BLOCK_COUNT];
		for (byte block : data) hostPresent[block & 0xFF] = true;
		final int CELL = 16, PAD = 4; // PAD must exceed the largest blob radius
		long gx0 = Math.floorDiv(baseX - PAD, (long) CELL), gx1 = Math.floorDiv(baseX + SIZE - 1 + PAD, (long) CELL);
		long gy0 = Math.floorDiv(baseY - PAD, (long) CELL), gy1 = Math.floorDiv(baseY + SIZE - 1 + PAD, (long) CELL);
		long gz0 = Math.floorDiv(baseZ - PAD, (long) CELL), gz1 = Math.floorDiv(baseZ + SIZE - 1 + PAD, (long) CELL);

		for (int t = 0; t < ORES.length; t++) {
			if (!hostPresent[ORE_HOST[t] & 0xFF]) continue;
			final int seed = 0x300 + t * 8;
			for (long gx = gx0; gx <= gx1; gx++)
				for (long gy = gy0; gy <= gy1; gy++)
					for (long gz = gz0; gz <= gz1; gz++) {
						int ix = (int) gx, iy = (int) gy, iz = (int) gz;
						if (hash3(ix, iy, iz, seed) * 100 >= ORE_PERCENT[t])
							continue;
						double ox = (gx + hash3(ix, iy, iz, seed + 1)) * CELL;
						double oy = (gy + hash3(ix, iy, iz, seed + 2)) * CELL;
						double oz = (gz + hash3(ix, iy, iz, seed + 3)) * CELL;
						double rad = ORE_R_MIN[t] + (ORE_R_MAX[t] - ORE_R_MIN[t]) * hash3(ix, iy, iz, seed + 4);
						double r2 = rad * rad;

						long x0 = Math.max(baseX, (long) Math.floor(ox - rad)), x1 = Math.min(baseX + SIZE - 1, (long) Math.ceil(ox + rad));
						long y0 = Math.max(baseY, (long) Math.floor(oy - rad)), y1 = Math.min(baseY + SIZE - 1, (long) Math.ceil(oy + rad));
						long z0 = Math.max(baseZ, (long) Math.floor(oz - rad)), z1 = Math.min(baseZ + SIZE - 1, (long) Math.ceil(oz + rad));

						for (long x = x0; x <= x1; x++)
							for (long y = y0; y <= y1; y++)
								for (long z = z0; z <= z1; z++) {
									double dx = x + 0.5 - ox, dy = y + 0.5 - oy, dz = z + 0.5 - oz;
									double d2 = dx * dx + dy * dy + dz * dz;
									if (d2 > r2)
										continue;
									if (d2 > r2 * 0.5 && hash3((int) x, (int) y, (int) z, seed + 5) < 0.4)
										continue; // ragged edges
									int idx = (int) (x - baseX) | ((int) (y - baseY) << SHIFT) | ((int) (z - baseZ) << (2 * SHIFT));
									if (data[idx] != ORE_HOST[t])
									    continue;

									if (ORES[t] == GOLD_ORE) {
										double depth = y - TBASE;
										double boundary = layer1(x, z);
										if (depth < boundary - 64 || depth >= boundary - LAYER_BLEND)
											continue;
									}

									if (ORE_HOST[t] != MOSS && isMossZone(x, y, z))
									    continue;

									data[idx] = ORES[t];
								}
					}
		}
	}

	private static void carveCaves(byte[] data, long cx, long cy, long cz) {
		long baseX = cx * SIZE, baseY = cy * SIZE, baseZ = cz * SIZE;

		final int n = CAVE_N;
		final int step = CAVE_STEP;
		final int nn = n * n;

		float[][] bufs = CAVE_G.get();
		float[] ga = bufs[0], gb = bufs[1];

		for (int gz = 0; gz < n; gz++)
			for (int gy = 0; gy < n; gy++)
				for (int gx = 0; gx < n; gx++) {
					double wx = (baseX + gx * step) * CAVE_XZ;
					double wy = (baseY + gy * step) * CAVE_Y;
					double wz = (baseZ + gz * step) * CAVE_XZ;

					int i = gz * nn + gy * n + gx;

					ga[i] = (float) (noise3(wx, wy, wz, 0x2A) * 2 - 1);
					gb[i] = (float) (noise3(wx, wy, wz, 0x6B) * 2 - 1);
				}

		int cells = SIZE / step;

		int[] off = {
			0, 1, n, n + 1,
			nn, nn + 1, nn + n, nn + n + 1
		};

		for (int kz = 0; kz < cells; kz++)
			for (int ky = 0; ky < cells; ky++)
				for (int kx = 0; kx < cells; kx++) {
					int i = kz * nn + ky * n + kx;

					float amin = Float.MAX_VALUE;
					float amax = -Float.MAX_VALUE;
					float bmin = Float.MAX_VALUE;
					float bmax = -Float.MAX_VALUE;

					for (int o : off) {
						float a = ga[i + o];
						float b = gb[i + o];

						if (a < amin) amin = a;
						if (a > amax) amax = a;
						if (b < bmin) bmin = b;
						if (b > bmax) bmax = b;
					}

					long cwx = baseX + kx * step, cwy = baseY + ky * step, cwz = baseZ + kz * step;
					double cellY = cwy + step / 2.0;

					// widest possible shell, so the early-out is valid for every biome
					double lim = CAVE_W * MOSS_K;
					if (amin > lim || amax < -lim || bmin > lim || bmax < -lim)
						continue;

					int biome = CB_NONE;
					double cellMoss = 0; // "zone weight" for whichever biome won
					for (int b : CB_ORDER) {
						cellMoss = zoneWeight(b, cwx, cellY, cwz);
						if (cellMoss > 0) { biome = b; break; }
					}
					double shellMul = 1 + (MOSS_K - 1) * cellMoss;

					for (int lz = 0; lz < step; lz++)
						for (int ly = 0; ly < step; ly++)
							for (int lx = 0; lx < step; lx++) {
								int x = kx * step + lx;
								int y = ky * step + ly;
								int z = kz * step + lz;

								int idx = x | (y << SHIFT) | (z << (2 * SHIFT));

								if (data[idx] == AIR)
									continue;

								// Smooth transition from thin surface caves to full-width deep caves.
								double worldY = baseY + y;
								double t = (worldY - CAVE_SURFACE_Y) / (CAVE_FULL_DENSITY_Y - CAVE_SURFACE_Y);
								t = Math.max(0.0, Math.min(1.0, t));
								t = t * t * (3.0 - 2.0 * t);

								double caveWidth = CAVE_SURFACE_WIDTH + (CAVE_W - CAVE_SURFACE_WIDTH) * t;
								double shell = caveWidth * shellMul;

								double fx = lx / (double) step;
								double fy = ly / (double) step;
								double fz = lz / (double) step;

								double a = tri(ga, i, n, fx, fy, fz);
								if (a > shell || a < -shell)
									continue;

								double b = tri(gb, i, n, fx, fy, fz);
								if (b > shell || b < -shell)
									continue;

								if (a <= caveWidth && a >= -caveWidth && b <= caveWidth && b >= -caveWidth) {
									data[idx] = AIR;
								} else if (cellMoss > 0.1 + 0.4 * hash3((int) (baseX + x), (int) (baseY + y), (int) (baseZ + z), 0x4D)) {
									if (replaceable(biome, data[idx]))
										data[idx] = CB_BLOCK[biome];
								}
							}
				}
	}

	private static final int[][] DIRS = { {1,0,0}, {-1,0,0}, {0,1,0}, {0,-1,0}, {0,0,1}, {0,0,-1} };
	private static final byte[] ICE_MAT = { ICE }, CRYSTAL_MAT = { RUBY, SAPPHIRE, AMETHYST, DIAMOND, QUARTZ };
	private static final int ICICLE_ODDS = 4; // 1 in N cells attempts an icicle (lower = denser)
	private static final int CRYSTAL_ICICLE_ODDS = 1; // 1 in N cells in crystal caves (1 = every cell tries)
	private static final int ICICLE_RETRIES = 8; // random re-rolls per cell when the spot is taken
	private static final int ICICLE_NONE = 0, ICICLE_BLOCKED = 1, ICICLE_GROWN = 2;

	private static boolean isIcicleBlock(byte b) {
		return b == ICE || b == RUBY || b == SAPPHIRE || b == AMETHYST || b == DIAMOND;
	}

	/** True if any of the 26 neighbours of this cell is already icicle material. */
	private static boolean icicleNearby(long wx, long wy, long wz) {
		for (byte dx = -1; dx <= 1; dx++)
			for (byte dy = -1; dy <= 1; dy++)
				for (byte dz = -1; dz <= 1; dz++)
					if (isIcicleBlock(getBlock(wx + dx, wy + dy, wz + dz)))
						return true;
		return false;
	}

	static final int GEM_SPIKE_ODDS = 2; // 1 in N crystal-cave cells

	private static void caveFeatures(long cx, long cy, long cz) {
		if (!caves)
			return;
		long baseX = cx * SIZE, baseY = cy * SIZE, baseZ = cz * SIZE;
		boolean snowY = baseY + SIZE > MOSS_Y0 && baseY < MOSS_Y3;
		boolean magmaY = baseY + SIZE > TBASE + LAYER2 - 300;
		Octree d = world.chunk(cx, cy, cz);
		if ((!snowY && !magmaY) || d == null || d == World.UNLOADED)
			return;
		Random r = new Random(World.key(cx, cy, cz) ^ 0x1C1C1EL);
		Random rg = new Random(World.key(cx, cy, cz) ^ 0x6E57C0L);
		for (int lx = 0; lx < SIZE; lx += 4)
			for (int ly = 0; ly < SIZE; ly += 4)
				for (int lz = 0; lz < SIZE; lz += 4) {
					int odds = ICICLE_ODDS;
					boolean crystal = magmaY && zoneAt(CB_CRYSTAL, baseX + lx + 2, baseY + ly + 2, baseZ + lz + 2) > 0;
					if (crystal) {
						odds = CRYSTAL_ICICLE_ODDS;
						if (rg.nextInt(GEM_SPIKE_ODDS) == 0)
							gemSpike(baseX + lx + rg.nextInt(4), baseY + ly + rg.nextInt(4), baseZ + lz + rg.nextInt(4), rg);
					}
					if (r.nextInt(odds) != 0)
						continue;
					growIcicle(baseX + lx, baseY + ly, baseZ + lz, r);
				}
	}

	static final int GEM_SPIKE_TRIES = 6;
	private static final long[][] GEM_PLUS = { {0,0,0}, {1,0,0}, {-1,0,0}, {0,0,1}, {0,0,-1} };

	/** 5-block plus on a crystal-cave surface plus one tip block (6 total). Half grow from the floor, half hang from the ceiling. +y is down. */
	private static void gemSpike(long cellX, long cellY, long cellZ, Random r) {
	    for (int t = 0; t < GEM_SPIKE_TRIES; t++) {
	        long x = cellX + r.nextInt(4), y = cellY + r.nextInt(4), z = cellZ + r.nextInt(4);
	        int s = r.nextBoolean() ? 1 : -1;               // 1 = floor below (y+1), -1 = ceiling above (y-1)
	        byte blk = r.nextBoolean() ? TANZANITE : RHODONITE;
	        if (getBlock(x, y + s, z) != ASH) continue;
	        boolean ok = getBlock(x, y - s, z) == AIR;      // tip cell
	        for (int i = 0; i < GEM_PLUS.length && ok; i++)
	            ok = getBlock(x + GEM_PLUS[i][0], y, z + GEM_PLUS[i][2]) == AIR;
	        if (!ok) continue;
	        for (long[] o : GEM_PLUS) setBlock(x + o[0], y, z + o[2], blk);
	        setBlock(x, y - s, z, blk);
	        return;
	    }
	}

	private static void growIcicle(long cellX, long cellY, long cellZ, Random r) {
		for (int attempt = 0; attempt < ICICLE_RETRIES; attempt++) {
			long x = cellX + r.nextInt(4), y = cellY + r.nextInt(4), z = cellZ + r.nextInt(4);
			if (icicle(x, y, z, DIRS[r.nextInt(6)], r, true) != ICICLE_BLOCKED)
				return; // grown, or not a valid spot at all (original behaviour)
		}
	}

	private static int icicle(long wx, long wy, long wz, int[] g, Random r, boolean needZone) {
		if (getBlock(wx, wy, wz) != AIR)
			return ICICLE_NONE;
		long sx = wx - g[0], sy = wy - g[1], sz = wz - g[2];
		byte base = getBlock(sx, sy, sz);
		int biome = base == SNOW ? CB_SNOW : base == ASH ? CB_CRYSTAL : CB_NONE;
		if (biome == CB_NONE || (needZone && zoneAt(biome, sx, sy, sz) <= 0))
			return ICICLE_NONE;
		if (icicleNearby(wx, wy, wz))
			return ICICLE_BLOCKED;
		byte[] mat = biome == CB_SNOW ? ICE_MAT : CRYSTAL_MAT;
		byte block = mat[r.nextInt(mat.length)];

		int ga = g[0] != 0 ? 0 : g[1] != 0 ? 1 : 2;
		double[] t = new double[3];
		if (r.nextInt(10) < 3) // diagonal tilt
			t[(ga + 1 + r.nextInt(2)) % 3] = (r.nextBoolean() ? 1 : -1) * (r.nextBoolean() ? 0.5 : 1.0);

		int len = 5 + r.nextInt(5);
		for (int i = 0; i < len; i++) {
			long x = wx + Math.round(g[0] * i + t[0] * i);
			long y = wy + Math.round(g[1] * i + t[1] * i);
			long z = wz + Math.round(g[2] * i + t[2] * i);
			if (getBlock(x, y, z) != AIR)
				break;
			setBlock(x, y, z, block);
			if (i > 1 && i < 4) {
				arm(x, y, z, (ga + 1) % 3, 1, block);  arm(x, y, z, (ga + 1) % 3, -1, block);
				arm(x, y, z, (ga + 2) % 3, 1, block);  arm(x, y, z, (ga + 2) % 3, -1, block);
			}
		}
		return ICICLE_GROWN;
	}

	private static void arm(long x, long y, long z, int axis, int s, byte block) {
		long[] c = { x, y, z };
		c[axis] += s;
		if (getBlock(c[0], c[1], c[2]) == AIR)
			setBlock(c[0], c[1], c[2], block);
	}

	/** First y in [baseY, baseY+SIZE) holding `a` or `b` with air directly above, or Long.MIN_VALUE. */
	private static long findSurface(long wx, long wz, long baseY, byte a, byte b) {
		for (long yy = baseY; yy < baseY + SIZE; yy++) {
			byte blk = getBlock(wx, yy, wz);
			if ((blk == a || blk == b) && getBlock(wx, yy - 1, wz) == AIR)
				return yy;
		}
		return Long.MIN_VALUE;
	}

	// Cave basins: big open chambers inside the slate layer
	static final int BASIN_CELL = 160, BASIN_PAD = 64, BASIN_PERCENT = 22; // % of cells that hold a basin
	static final int BASIN_TRIES = 160, BASIN_TREE_TRIES = 14;
	private static final int[] DOWN = { 0, 1, 0 }, UP = { 0, -1, 0 }; // +y is down in this world

	private static final class BasinEntry {
	    final long gx, gz; final double[] b;
	    BasinEntry(long gx, long gz, double[] b) { this.gx = gx; this.gz = gz; this.b = b; }
	}
	private static final ConcurrentHashMap<Long, BasinEntry> BASIN_CACHE = new ConcurrentHashMap<>();

	/** {ox, oy, oz, rx, ry, rz, biome} for the basin owned by this 2D cell, or null. Returned arrays are read-only. */
	private static double[] basinAt(long gx, long gz) {
	    long k = gx * 0x9E3779B97F4A7C15L ^ Long.rotateLeft(gz * 0xC2B2AE3D27D4EB4FL, 31);
	    BasinEntry e = BASIN_CACHE.get(k);
	    if (e != null && e.gx == gx && e.gz == gz) return e.b;
	    double[] b = computeBasin(gx, gz);
	    if (BASIN_CACHE.size() > 8192) BASIN_CACHE.clear();
	    BASIN_CACHE.put(k, new BasinEntry(gx, gz, b));
	    return b;
	}

	/** {ox, oy, oz, rx, ry, rz, biome} for the basin owned by this 2D cell, or null. */
	private static double[] computeBasin(long gx, long gz) {
		int ix = (int) gx, iz = (int) gz;
		if (hash3(ix, 0, iz, 0xBA5) * 100 >= BASIN_PERCENT)
			return null;
		double ox = (gx + 0.2 + 0.6 * hash3(ix, 0, iz, 0xBA6)) * BASIN_CELL;
		double oz = (gz + 0.2 + 0.6 * hash3(ix, 0, iz, 0xBA7)) * BASIN_CELL;
		double rx = 22 + 18 * hash3(ix, 0, iz, 0xBA8), rz = 22 + 18 * hash3(ix, 0, iz, 0xBA9);
		double ry = 14 + 8 * hash3(ix, 0, iz, 0xBAA); // tall enough for trees
		double lo = layer1(ox, oz) + ry + 24;
		double hi = Math.min(layer2(ox, oz) - ry - 8, BASIN_MAX_Y - TBASE - ry); // oy = TBASE + (lo..hi)
		if (hi <= lo)
			return null;
		double oy = TBASE + lo + (hi - lo) * hash3(ix, 0, iz, 0xBAB);
		int biome = noise(ox / 512.0, oz / 512.0) > 1.4 ? CB_SNOW : CB_MOSS; // snow only under snowy biomes
		return new double[] { ox, oy, oz, rx, ry, rz, biome };
	}

	private static double basinRaw(double[] b, double x, double y, double z) {
		double dx = (x - b[0]) / b[3], dy = (y - b[1]) / b[4], dz = (z - b[2]) / b[5];
		return dx * dx + dy * dy + dz * dz;
	}

	/** Ellipsoid distance (<= 1 is inside) with a noisy, lumpy outline. */
	private static double basinShape(double[] b, double x, double y, double z) {
		double wob = 1 + 0.25 * (noise3(x / 18.0, y / 14.0, z / 18.0, 0xBAC) - 0.5);
		return basinRaw(b, x, y, z) / (wob * wob);
	}

	/** Flat-ish floor with gentle bumps. */
	private static double basinFloor(double[] b, double x, double z) {
		return b[1] + 0.4 * b[4] + (noise3(x / 12.0, 0, z / 12.0, 0xBAD) - 0.5) * 3;
	}

	private static byte basinBlock(double[] b, double fd) {
		boolean snow = (int) b[6] == CB_SNOW;
		if (fd > 0) // floor
			return snow ? SNOW : (fd <= 1 ? GRASS : DIRT); // grass floor so trees can grow
		return snow ? SNOW : MOSS;
	}

	private static void carveBasins(byte[] data, long cx, long cy, long cz) {
		if (cy * SIZE > BASIN_MAX_Y + 64)
			return;
		long baseX = cx * SIZE, baseY = cy * SIZE, baseZ = cz * SIZE;
		if (baseY + SIZE - 1 < TBASE + 40)
			return; // basins never get this shallow
		for (long gx = Math.floorDiv(baseX - BASIN_PAD, (long) BASIN_CELL); gx <= Math.floorDiv(baseX + SIZE - 1 + BASIN_PAD, (long) BASIN_CELL); gx++)
			for (long gz = Math.floorDiv(baseZ - BASIN_PAD, (long) BASIN_CELL); gz <= Math.floorDiv(baseZ + SIZE - 1 + BASIN_PAD, (long) BASIN_CELL); gz++) {
				double[] b = basinAt(gx, gz);
				if (b != null)
					shapeBasin(data, b, baseX, baseY, baseZ);
			}
	}

	/** Returns the nearest basin's cave-biome fog type near/inside a basin. */
	static int basinFogBiome(long wx, long wy, long wz) {
		if (wy > BASIN_MAX_Y + 64 || wy < TBASE + 40)
			return CB_NONE;
		long gx0 = Math.floorDiv(wx, (long) BASIN_CELL), gz0 = Math.floorDiv(wz, (long) BASIN_CELL);
		double best = Double.POSITIVE_INFINITY;
		int result = CB_NONE;
		for (long gx = gx0 - 1; gx <= gx0 + 1; gx++)
			for (long gz = gz0 - 1; gz <= gz0 + 1; gz++) {
				double[] basin = basinAt(gx, gz);
				if (basin == null) continue;
				double shape = basinShape(basin, wx + 0.5, wy + 0.5, wz + 0.5);
				// Expand the basin's biome influence into nearby cave space. The fog
				// renderer uses this as a hard override, so adjacent cave types cannot
				// create competing dark patches around a basin.
				if (shape < best && shape < 3.0) { best = shape; result = (int) basin[6]; }
			}
		return result;
	}

	/** Smooth influence around the basin edge; prevents abrupt fog patches in nearby caves. */
	static double basinFogWeight(long wx, long wy, long wz) {
		if (wy > BASIN_MAX_Y + 64 || wy < TBASE + 40) return 0;
		long gx0 = Math.floorDiv(wx, (long) BASIN_CELL), gz0 = Math.floorDiv(wz, (long) BASIN_CELL);
		double weight = 0;
		for (long gx = gx0 - 1; gx <= gx0 + 1; gx++)
			for (long gz = gz0 - 1; gz <= gz0 + 1; gz++) {
				double[] basin = basinAt(gx, gz);
				if (basin == null) continue;
				double shape = basinShape(basin, wx + 0.5, wy + 0.5, wz + 0.5);
				// Full basin tint in the chamber, feathered out over the irregular rim.
				weight = Math.max(weight, 1.0 - smoothstep(0.78, 1.65, shape));
			}
		return weight;
	}

	/** Locate a real cave-noise air point near the basin; candidates are deterministic. */
	private static double[] basinCaveTarget(double[] b) {
		double best = Double.POSITIVE_INFINITY;
		double[] target = null;
		int[] dirs = { 0, 1, 2, 3, 4, 5, 6, 7 };
		for (int d : dirs) {
			double angle = d * (Math.PI / 4.0);
			for (int dist = (int) Math.ceil(Math.max(b[3], b[5])) + 4; dist <= Math.max(b[3], b[5]) + 36; dist += 4)
				for (int yo = -16; yo <= 16; yo += 8) {
				double x = b[0] + Math.cos(angle) * dist;
				double y = b[1] + yo;
				double z = b[2] + Math.sin(angle) * dist;
				if (y < TBASE + 40 || y > BASIN_MAX_Y + 64 || basinShape(b, x, y, z) <= 1.15 || !caveAir(x, y, z))
					continue;
				double score = dist * dist + yo * yo;
				if (score < best) {
					best = score;
					target = new double[] { x, y, z };
				}
				}
		}
		return target;
	}

	private static void shapeBasin(byte[] data, double[] b, long baseX, long baseY, long baseZ) {
		long x0 = Math.max(baseX, (long) Math.floor(b[0] - b[3] * 1.5)), x1 = Math.min(baseX + SIZE - 1, (long) Math.ceil(b[0] + b[3] * 1.5));
		long y0 = Math.max(baseY, (long) Math.floor(b[1] - b[4] * 1.5)), y1 = Math.min(baseY + SIZE - 1, (long) Math.ceil(b[1] + b[4] * 1.2));
		long z0 = Math.max(baseZ, (long) Math.floor(b[2] - b[5] * 1.5)), z1 = Math.min(baseZ + SIZE - 1, (long) Math.ceil(b[2] + b[5] * 1.5));
		double floorCap = b[1] + 0.4 * b[4];
		for (long x = x0; x <= x1; x++)
			for (long y = y0; y <= y1; y++)
				for (long z = z0; z <= z1; z++) {
					double px = x + 0.5, py = y + 0.5, pz = z + 0.5;
					if (basinRaw(b, px, Math.min(py, floorCap), pz) > 1.7)
						continue; // cheap cull before any noise
					int idx = (int) (x - baseX) | ((int) (y - baseY) << SHIFT) | ((int) (z - baseZ) << (2 * SHIFT));
					if (data[idx] == AIR)
						continue;
					double fl = basinFloor(b, px, pz), s = basinShape(b, px, py, pz), fd = py - fl;
					if (fd <= 0 && s <= 1) {
						data[idx] = AIR;
						continue;
					}
					// coat the shell: ceiling/walls (fd <= 0) or the 3 blocks under the floor
					boolean shell = fd > 0 ? fd <= 3 && basinShape(b, px, floorCap, pz) <= 1.3 : s <= 1.3;
					byte cur = data[idx];
					if (shell && (cur == STONE || cur == SLATE))
						data[idx] = basinBlock(b, fd);
				}

		// Short connector: find an actual point in the generated cave noise just
		// outside the basin, then carve only the path needed to reach that cave.
		double[] target = basinCaveTarget(b);
		if (target != null) {
			double dx = target[0] - b[0], dy = target[1] - b[1], dz = target[2] - b[2];
			int steps = (int) Math.ceil(Math.sqrt(dx * dx + dy * dy + dz * dz) * 1.5);
			for (int i = 0; i <= steps; i++) {
				double t = i / (double) Math.max(1, steps);
				double px = b[0] + dx * t, py = b[1] + dy * t, pz = b[2] + dz * t;
				long ax = (long) Math.floor(px - 2.5), bx = (long) Math.ceil(px + 2.5);
				long ay = (long) Math.floor(py - 2.5), by = (long) Math.ceil(py + 2.5);
				long az = (long) Math.floor(pz - 2.5), bz = (long) Math.ceil(pz + 2.5);
				for (long x = Math.max(baseX, ax); x <= Math.min(baseX + SIZE - 1, bx); x++)
					for (long y = Math.max(baseY, ay); y <= Math.min(baseY + SIZE - 1, by); y++)
						for (long z = Math.max(baseZ, az); z <= Math.min(baseZ + SIZE - 1, bz); z++) {
							double qx = x + 0.5 - px, qy = y + 0.5 - py, qz = z + 0.5 - pz;
							if (qx*qx + qy*qy + qz*qz <= 6.25) {
								int idx = (int) (x - baseX) | ((int) (y - baseY) << SHIFT) | ((int) (z - baseZ) << (2 * SHIFT));
								data[idx] = AIR;
							}
						}
			}
		}
	}

	private static void basinFeatures(long cx, long cy, long cz) {
		if (cy * SIZE > BASIN_MAX_Y + 64)
			return;
		if (!caves)
			return;
		long baseX = cx * SIZE, baseY = cy * SIZE, baseZ = cz * SIZE;
		if (baseY + SIZE - 1 < TBASE + 40)
			return;
		for (long gx = Math.floorDiv(baseX - BASIN_PAD, (long) BASIN_CELL); gx <= Math.floorDiv(baseX + SIZE - 1 + BASIN_PAD, (long) BASIN_CELL); gx++)
			for (long gz = Math.floorDiv(baseZ - BASIN_PAD, (long) BASIN_CELL); gz <= Math.floorDiv(baseZ + SIZE - 1 + BASIN_PAD, (long) BASIN_CELL); gz++) {
				double[] b = basinAt(gx, gz);
				if (b == null)
					continue;
				Random r = new Random(World.key(cx, cy, cz) ^ (gx * 31 + gz) ^ 0xBA51L);
				if ((int) b[6] == CB_SNOW)
					basinIcicles(b, r, baseX, baseY, baseZ);
				else
					basinTrees(b, r, baseX, baseY, baseZ);
			}
	}

	private static void basinIcicles(double[] b, Random r, long baseX, long baseY, long baseZ) {
		for (int i = 0; i < BASIN_TRIES; i++) {
			long x = baseX + r.nextInt(SIZE), y = baseY + r.nextInt(SIZE), z = baseZ + r.nextInt(SIZE);
			if (basinShape(b, x + 0.5, y + 0.5, z + 0.5) > 0.9)
				continue;
			int roll = r.nextInt(100);
			int[] g = roll < 55 ? DOWN : roll < 80 ? UP : DIRS[r.nextInt(6)]; // mostly hanging from the ceiling
			long[] s = seekSurface(x, y, z, g, 48);
			if (s != null)
				icicle(s[0], s[1], s[2], g, r, false);
		}
	}

	private static void basinTrees(double[] b, Random r, long baseX, long baseY, long baseZ) {
		for (int i = 0; i < BASIN_TREE_TRIES; i++) {
			long x = baseX + r.nextInt(SIZE), z = baseZ + r.nextInt(SIZE);
			double dx = (x - b[0]) / b[3], dz = (z - b[2]) / b[5];
			if (dx * dx + dz * dz > 0.55)
				continue; // keep trees off the sloped edges
			long ty = findSurface(x, z, baseY, GRASS, GRASS);
			if (ty == Long.MIN_VALUE || Math.abs(ty - b[1]) > b[4] * 1.5)
				continue; // not this basin's floor
			int th = 4 + r.nextInt(2);
			boolean clear = true;
			for (long yy = ty - 1; yy >= ty - th - 2 && clear; yy--)
				clear = getBlock(x, yy, z) == AIR;
			if (clear)
				buildTree(x, ty, z, th, r);
		}
	}

	/** Walks from an air cell backwards along growth direction g to the wall; returns the last air cell. */
	private static long[] seekSurface(long x, long y, long z, int[] g, int max) {
		if (getBlock(x, y, z) != AIR)
			return null;
		for (int i = 0; i < max; i++) {
			if (getBlock(x - g[0], y - g[1], z - g[2]) != AIR)
				return new long[] { x, y, z };
			x -= g[0]; y -= g[1]; z -= g[2];
		}
		return null;
	}


	// ---- Surface Menger sponges ----
	// Candidates are world-grid aligned, so each intersecting chunk independently generates its own slice.
	private static final int MENGER_CELL = 1024;
	private static final int MENGER_MAX_SIZE = 81;

	private static long mengerSurfaceY(long wx, long wz) {
		if (!terrain3D) return terrainHeight(wx, wz);
		double half = 0.5 * TK * Math.abs(amp) * TDIV;
		long lo = (long) Math.floor(TBASE - half) - 2;
		long hi = (long) Math.ceil(TBASE + half) + 2;
		// Density increases toward the deeper (+Y) side in the current coordinate system.
		for (int i = 0; i < 64 && hi - lo > 1; i++) {
			long mid = lo + (hi - lo) / 2;
			if (density(wx, mid, wz) > 0) hi = mid; else lo = mid;
		}
		return hi - 1;
	}

	private static final class MengerSite {
	    final long gx, gz, ax, az, surface; final int size; final byte block; final boolean valid;
	    MengerSite(long gx, long gz) { this.gx = gx; this.gz = gz; ax = az = surface = 0; size = 0; block = AIR; valid = false; }
	    MengerSite(long gx, long gz, long ax, long az, long surface, int size, byte block) {
	        this.gx = gx; this.gz = gz; this.ax = ax; this.az = az; this.surface = surface; this.size = size; this.block = block; valid = true;
	    }
	}
	private static final ConcurrentHashMap<Long, MengerSite> MENGER_SITES = new ConcurrentHashMap<>();

	private static MengerSite mengerSite(long gx, long gz) {
	    long k = gx * 0x9E3779B97F4A7C15L ^ Long.rotateLeft(gz * 0xC2B2AE3D27D4EB4FL, 31);
	    MengerSite s = MENGER_SITES.get(k);
	    if (s != null && s.gx == gx && s.gz == gz) return s;
	    s = computeMengerSite(gx, gz);
	    if (MENGER_SITES.size() > 4096) MENGER_SITES.clear();
	    MENGER_SITES.put(k, s);
	    return s;
	}

	private static MengerSite computeMengerSite(long gx, long gz) {
	    int ix = (int) gx, iz = (int) gz;
	    long ax = gx * MENGER_CELL + 32 + (long) (hash3(ix, 0, iz, 0x4D5351) * (MENGER_CELL - 64));
	    long az = gz * MENGER_CELL + 32 + (long) (hash3(ix, 0, iz, 0x4D5352) * (MENGER_CELL - 64));
	    double plains = plainsAt(ax, az);
	    double terrainRoll = hash3(ix, 0, iz, 0x4D5353);
	    if (plains < 0.65 ? terrainRoll > 0.50 : terrainRoll > 0.72) return new MengerSite(gx, gz); // cheap reject first
	    double slope = Math.max(
	        Math.max(Math.abs(mengerSurfaceY(ax - 12, az) - mengerSurfaceY(ax + 12, az)),
	                 Math.abs(mengerSurfaceY(ax, az - 12) - mengerSurfaceY(ax, az + 12))),
	        Math.max(Math.abs(mengerSurfaceY(ax - 12, az - 12) - mengerSurfaceY(ax + 12, az + 12)),
	                 Math.abs(mengerSurfaceY(ax - 12, az + 12) - mengerSurfaceY(ax + 12, az - 12))));
	    if (plains < 0.65 ? slope > 32 : slope > 14) return new MengerSite(gx, gz);
	    double iterRoll = hash3(ix, 0, iz, 0x4D5354);
	    int size = iterRoll < 0.60 ? 9 : iterRoll < 0.90 ? 27 : 81;
	    byte block = new Random(World.key(gx, 0, gz) ^ 0x4D454E474552L).nextBoolean() ? BRICKS : OAK_PLANKS;
	    return new MengerSite(gx, gz, ax, az, mengerSurfaceY(ax, az), size, block);
	}

	private static void mengerSpongeFeatures(long cx, long cy, long cz) {
	    long baseX = cx * SIZE, baseY = cy * SIZE, baseZ = cz * SIZE;
	    long gx0 = Math.floorDiv(baseX - MENGER_CELL - MENGER_MAX_SIZE / 2, (long) MENGER_CELL);
	    long gx1 = Math.floorDiv(baseX + SIZE + MENGER_MAX_SIZE / 2, (long) MENGER_CELL);
	    long gz0 = Math.floorDiv(baseZ - MENGER_CELL - MENGER_MAX_SIZE / 2, (long) MENGER_CELL);
	    long gz1 = Math.floorDiv(baseZ + SIZE + MENGER_MAX_SIZE / 2, (long) MENGER_CELL);
	    for (long gx = gx0; gx <= gx1; gx++) for (long gz = gz0; gz <= gz1; gz++) {
	        MengerSite s = mengerSite(gx, gz);
	        if (!s.valid) continue;
	        final int size = s.size; final long ax = s.ax, az = s.az, surface = s.surface; final byte block = s.block;
	        long topY = surface - size + 1;
	        if (baseY > surface || baseY + SIZE <= topY) continue;
	        long x0 = Math.max(baseX, ax - size / 2), x1 = Math.min(baseX + SIZE - 1, ax - size / 2 + size - 1);
	        long y0 = Math.max(baseY, topY), y1 = Math.min(baseY + SIZE - 1, surface);
	        long z0 = Math.max(baseZ, az - size / 2), z1 = Math.min(baseZ + SIZE - 1, az - size / 2 + size - 1);
	        if (x0 > x1 || y0 > y1 || z0 > z1) continue;
	        for (long wx = x0; wx <= x1; wx++) for (long wy = y0; wy <= y1; wy++) for (long wz = z0; wz <= z1; wz++) {
	            int lx = (int) (wx - (ax - size / 2)), ly = (int) (wy - topY), lz = (int) (wz - (az - size / 2));
	            if (mengerSolid(lx, ly, lz)) setBlock(wx, wy, wz, block);
	            else if (getBlock(wx, wy, wz) != AIR) setBlock(wx, wy, wz, AIR);
	        }
	    }
	}

	private static boolean mengerSolid(int x, int y, int z) {
		while (x > 0 || y > 0 || z > 0) {
			int middle = (x % 3 == 1 ? 1 : 0) + (y % 3 == 1 ? 1 : 0) + (z % 3 == 1 ? 1 : 0);
			if (middle >= 2) return false;
			x /= 3; y /= 3; z /= 3;
		}
		return true;
	}

	// ---- Autumn forest: rare, plains only, autumn grass + dense birch trees ----
	static final double AUTUMN_BIOME_MIN = 0.8, AUTUMN_BIOME_MAX = 1.3; // same "plains" band the locator uses
	static final double AUTUMN_SCALE = 300, AUTUMN_THRESHOLD = 0.85;
	static final byte AUTUMN_TREE_SPACING = 4, AUTUMN_TREE_PERCENT = 80; // grid step and % of cells that try a tree
	private static final byte[] AUTUMN_LEAVES = { RED_LEAVES, ORANGE_LEAVES, YELLOW_LEAVES };

	static boolean isAutumnForest(long wx, long wz) {
		return isAutumnForest(wx, wz, noise(wx / 512.0, wz / 512.0));
	}

	/** biomeVal is the already computed noise(wx / 512, wz / 512). */
	static boolean isAutumnForest(long wx, long wz, double biomeVal) {
		if (biomeVal < AUTUMN_BIOME_MIN || biomeVal > AUTUMN_BIOME_MAX)
			return false;
		return noise3(wx / AUTUMN_SCALE, 0, wz / AUTUMN_SCALE, 0xAF7) > AUTUMN_THRESHOLD;
	}

	private static boolean autumnChunkPossible(long baseX, long baseZ) {
	    long fx0 = (long) Math.floor((baseX - 2) / AUTUMN_SCALE), fx1 = (long) Math.floor((baseX + SIZE + 2) / AUTUMN_SCALE);
	    long fz0 = (long) Math.floor((baseZ - 2) / AUTUMN_SCALE), fz1 = (long) Math.floor((baseZ + SIZE + 2) / AUTUMN_SCALE);
	    for (long xi = fx0; xi <= fx1 + 1; xi++)
	        for (long zi = fz0; zi <= fz1 + 1; zi++)
	            if (hash3((int) xi, 0, (int) zi, 0xAF7) > AUTUMN_THRESHOLD) return true;
	    return false;
	}

	private static void autumnForestFeatures(long cx, long cy, long cz) {
		long baseX = cx * SIZE, baseY = cy * SIZE, baseZ = cz * SIZE;
		Octree d = world.chunk(cx, cy, cz);
		if (d == null || d == World.UNLOADED || !autumnChunkPossible(baseX, baseZ))
			return;
		if (terrain3D) {
			double half = 0.5 * TK * Math.abs(amp) * TDIV;
			if (baseY + SIZE < TBASE - half - 32 || baseY > TBASE + half + 32)
				return;
		}

		Random r = new Random(World.key(cx, cy, cz) ^ 0xA07F0E57L);

		// No chunk-border margin: attempt trees across the entire chunk.
		for (int lx = 0; lx < SIZE; lx += AUTUMN_TREE_SPACING) {
			for (int lz = 0; lz < SIZE; lz += AUTUMN_TREE_SPACING) {
				if (r.nextInt(100) >= AUTUMN_TREE_PERCENT)
					continue;

				long tx = baseX + lx + r.nextInt(3) - 1;
				long tz = baseZ + lz + r.nextInt(3) - 1;

				plantAutumnTree(tx, tz, baseY, r);
			}
		}
	}

	private static void plantAutumnTree(long tx, long tz, long baseY, Random r) {
		int th = 5 + r.nextInt(3);

		if (!isAutumnForest(tx, tz))
			return;

		long ty = findSurface(tx, tz, baseY, AUTUMN_GRASS, AUTUMN_GRASS);
		if (ty == Long.MIN_VALUE)
			return;

		for (long yy = ty - 1; yy >= ty - th - 2; yy--)
			if (getBlock(tx, yy, tz) != AIR)
				return;

		buildAutumnTree(tx, ty, tz, th, r);
	}

	private static void buildAutumnTree(long x, long terrainY, long z, int h, Random rand) {
		// Birch trunk
		for (long yy = terrainY - 1; yy >= terrainY - h; yy--) {
			setBlock(x, yy, z, BIRCH_LOG);
			byte under = getBlock(x, yy + 1, z);
			if (under == GRASS || under == AUTUMN_GRASS)
				setBlock(x, yy + 1, z, DIRT);
		}

		// Main canopy: independently scramble each leaf block's colour
		fillAutumnLeaves(x - 2, terrainY - h + 1, z - 2, x + 3, terrainY - h + 3, z + 3, rand);
		fillAutumnLeaves(x - 1, terrainY - h - 1, z - 1, x + 2, terrainY - h + 1, z + 2, rand);

		long[] fxL = { x - 2, x - 2, x + 2, x + 2 };
		long[] fzL = { z - 2, z + 2, z + 2, z - 2 };
		long[] cxL = { x - 1, x - 1, x + 1, x + 1 };
		long[] czL = { z - 1, z + 1, z + 1, z - 1 };

		for (int i = 0; i < 4; i++) {
			switch (rand.nextInt(10)) {
			case 0:
				setBlock(fxL[i], terrainY - h + 1, fzL[i], AIR);
				break;
			case 1:
				setBlock(fxL[i], terrainY - h + 2, fzL[i], AIR);
				break;
			case 2:
				setBlock(fxL[i], terrainY - h + 1, fzL[i], AIR);
				setBlock(fxL[i], terrainY - h + 2, fzL[i], AIR);
				break;
			}

			if (rand.nextInt(10) == 0) {
				setBlock(cxL[i], terrainY - h - 1, czL[i], AIR);
				setBlock(cxL[i], terrainY - h, czL[i], AIR);
			} else {
				setBlock(cxL[i], terrainY - h - 1, czL[i], AIR);
			}
		}
	}


	private static void fillAutumnLeaves(long x1, long y1, long z1, long x2, long y2, long z2, Random rand) {
		for (long x = x1; x < x2; x += 2) {
			for (long y = y1; y < y2; y += 2) {
				for (long z = z1; z < z2; z += 2) {
					byte leaf = AUTUMN_LEAVES[rand.nextInt(AUTUMN_LEAVES.length)];
					for (long dx = 0; dx < 2 && x + dx < x2; dx++) {
						for (long dy = 0; dy < 2 && y + dy < y2; dy++) {
							for (long dz = 0; dz < 2 && z + dz < z2; dz++) {
								// Preserve trunks: canopy generation must never overwrite birch logs.
							long bx = x + dx, by = y + dy, bz = z + dz;
							if (getBlock(bx, by, bz) != BIRCH_LOG && getBlock(bx, by, bz) == AIR)
								setBlock(bx, by, bz, leaf);
							}
						}
					}
				}
			}
		}
	}

	/** Exactly new Random(seed).nextInt(bound) for a non-power-of-two bound, without allocating. */
	private static int firstInt(long seed, int bound) {
	    final long mask = (1L << 48) - 1;
	    long s = (seed ^ 0x5DEECE66DL) & mask;
	    for (;;) {
	        s = (s * 0x5DEECE66DL + 0xBL) & mask;
	        int u = (int) (s >>> 17), r = u % bound;
	        if (u - r + (bound - 1) >= 0) return r;
	    }
	}

	private static void features(long cx, long cy, long cz) {
	    long baseX = cx * SIZE, baseY = cy * SIZE, baseZ = cz * SIZE;
	    long colKey = World.key(cx, 0, cz);
	    for (int lx = 3; lx < SIZE - 3; lx += 6) {
	        for (int lz = 3; lz < SIZE - 3; lz += 6) {
	            long wx = baseX + lx, wz = baseZ + lz;
	            long cell = colKey * 31 + lx * 7 + lz;

	            long iceSeed = cell ^ 0x51F1CEL;
	            if (firstInt(iceSeed, 20) == 0 && noise(wx / 512.0, wz / 512.0) >= 1.45) {
	                Random r = new Random(iceSeed);
	                r.nextInt(20); // replay the draw firstInt() already did
	                int h = 6 + r.nextInt(6);
	                long ty = findSurface(wx, wz, baseY, SNOW, ICE);
	                if (ty != Long.MIN_VALUE) {
	                    for (int yo = 0; yo < h; yo++) {
	                        setBlock(wx, ty - yo, wz, ICE);
	                        if (yo > 1 && yo < 4) {
	                            setBlock(wx + 1, ty - yo, wz, ICE);
	                            setBlock(wx - 1, ty - yo, wz, ICE);
	                            setBlock(wx, ty - yo, wz + 1, ICE);
	                            setBlock(wx, ty - yo, wz - 1, ICE);
	                        }
	                    }
	                }
	            }

	            long treeSeed = cell ^ 0x7123L;
	            if (firstInt(treeSeed, 6) != 0) continue;
	            Random r = new Random(treeSeed);
	            r.nextInt(6);
	            long tx = wx + r.nextInt(32) - 16;
	            long tz = wz + r.nextInt(32) - 16;
	            int th = 4 + r.nextInt(2);
	            double val = noise(tx / 512.0, tz / 512.0);
	            if (val < 0.7 || val > 1.35) continue;
	            long ty = findSurface(tx, tz, baseY, GRASS, GRASS);
	            if (ty == Long.MIN_VALUE) continue;
	            boolean clear = true;
	            for (long yy = ty - 1; yy >= ty - th - 2; yy--)
	                if (getBlock(tx, yy, tz) != AIR) { clear = false; break; }
	            if (clear) buildTree(tx, ty, tz, th, r);
	        }
	    }
	}

	private static void buildTree(long x, long terrainY, long z, int h, Random rand) {
		buildTree(x, terrainY, z, h, rand, OAK_LOG, LEAVES);
	}

	/** Trunk grows upward (decreasing y) from terrainY - 1. */
	private static void buildTree(long x, long terrainY, long z, int h, Random rand, byte log, byte leaves) {
		for (long yy = terrainY - 1; yy >= terrainY - h; yy--) {
			setBlock(x, yy, z, log);
			byte under = getBlock(x, yy + 1, z);
			if (under == GRASS || under == AUTUMN_GRASS)
				setBlock(x, yy + 1, z, DIRT);
		}
		fill(leaves, x - 2, terrainY - h + 1, z - 2, x + 3, terrainY - h + 3, z + 3, false);
		fill(leaves, x - 1, terrainY - h - 1, z - 1, x + 2, terrainY - h + 1, z + 2, false);
		long[] fxL = { x - 2, x - 2, x + 2, x + 2 };
		long[] fzL = { z - 2, z + 2, z + 2, z - 2 };
		long[] cxL = { x - 1, x - 1, x + 1, x + 1 };
		long[] czL = { z - 1, z + 1, z + 1, z - 1 };
		for (int i = 0; i < 4; i++) {
			switch (rand.nextInt(10)) {
			case 0:
				setBlock(fxL[i], terrainY - h + 1, fzL[i], AIR);
				break;
			case 1:
				setBlock(fxL[i], terrainY - h + 2, fzL[i], AIR);
				break;
			case 2:
				setBlock(fxL[i], terrainY - h + 1, fzL[i], AIR);
				setBlock(fxL[i], terrainY - h + 2, fzL[i], AIR);
				break;
			}
			if (rand.nextInt(10) == 0) {
				setBlock(cxL[i], terrainY - h - 1, czL[i], AIR);
				setBlock(cxL[i], terrainY - h, czL[i], AIR);
			} else {
				setBlock(cxL[i], terrainY - h - 1, czL[i], AIR);
			}
		}
	}

	// ------------------------------------------------------------------ block access

	static byte getBlock(long x, long y, long z) {
		Octree c = world.chunk(x >> SHIFT, y >> SHIFT, z >> SHIFT);
		if (c == null || c == World.UNLOADED)
			return AIR;
		return c.get((byte) (x & MASK), (byte) (y & MASK), (byte) (z & MASK));
	}

	static void setBlock(long x, long y, long z, byte block) {
		long cx = x >> SHIFT, cy = y >> SHIFT, cz = z >> SHIFT;
		long ck = World.key(cx, cy, cz);
		if (generating && ck != homeKey) {
			defer(ck, x, y, z, block);
			return; // Replay cross-chunk feature writes later instead of mutating another chunk now.
		}
		int s = world.slot(cx, cy, cz);
		if (world.keys[s] != ck)
			return;
		Octree c = world.data[s];
		final byte prev = c == null ? AIR : c.get((byte) (x & MASK), (byte) (y & MASK), (byte) (z & MASK));
		if (c == null) {
			if (block == AIR)
				return;
			c = world.data[s] = new Octree(64);
		} else if (c.shared) {
			if (c.root == (Octree.LEAF | (block & 0xFF)))
				return;
			c = world.data[s] = c.copy();
		}
		if (!c.set((int) (x & MASK), (int) (y & MASK), (int) (z & MASK), block))
			return;
		if (emits(prev) || emits(block)) lightVer++;
		world.dirty[s] = true;
		if (generating) {
			streamVer++;
		} else {
			worldVer++;
			world.user[s] = true;
		}
		if (block != AIR && y < userTopY) userTopY = y;
		if (c.isEmpty())
			world.data[s] = null;
	}

	private static void fill(byte block, long x0, long y0, long z0, long x1, long y1, long z1, boolean replace) {
		for (long x = x0; x < x1; x++)
			for (long y = y0; y < y1; y++)
				for (long z = z0; z < z1; z++) {
					if (!replace && getBlock(x, y, z) != AIR)
						continue;
					setBlock(x, y, z, block);
				}
	}

	static volatile boolean copyMode;
	static final boolean COPY_AIR = true;           // false = air in the source leaves the destination untouched
	static final long COPY_MAX_VOXELS = 1L << 25;

	private static boolean inPlayerBlocks(long[] pm, long dx, long dy, long dz) {
		for (byte k = 0; k < 36; k += 3)
			if (pm[k] == dx && pm[k + 1] == dy && pm[k + 2] == dz) return true;
		return false;
	}

	private static void copyRegion(long x0, long y0, long z0, long x1, long y1, long z1) {
		long sx = x1 - x0, sy = y1 - y0, sz = z1 - z0;
		if (sx * sy * sz > COPY_MAX_VOXELS) { say("Copy region too large"); return; }
		final long ox = floorOf(x), oz = floorOf(z), oy = blockAt(y, 1.45) - (sy - 1);
		final long[] pm = new long[36]; // the 12 blocks the player occupies: never paste into the player
		for (int c = 0; c < 12; c++) {
			pm[c * 3] = blockAt(x, (c & 1) * 0.6 - 0.3);
			pm[c * 3 + 1] = blockAt(y, ((c >> 2) - 1) * 0.8 + 0.65);
			pm[c * 3 + 2] = blockAt(z, (c >> 1 & 1) * 0.6 - 0.3);
		}
		byte[] buf = new byte[(int) (sx * sy * sz)]; // read everything first so overlapping copies are safe
		int n = 0;
		for (long a = x0; a < x1; a++)
			for (long b = y0; b < y1; b++)
				for (long c = z0; c < z1; c++)
					buf[n++] = getBlock(a, b, c);
		if (survival) {                                          // pass 1: price the paste, then pay all-or-nothing
			long[] need = new long[256], repl = new long[256];
			n = 0;
			for (long a = 0; a < sx; a++)
				for (long b = 0; b < sy; b++)
					for (long c = 0; c < sz; c++) {
						byte blk = buf[n++];
						long dx = ox + a, dy = oy + b, dz = oz + c;
						if (blk != AIR && inPlayerBlocks(pm, dx, dy, dz)) continue;
						if (!isLoaded(dx, dy, dz)) continue;
						byte cur = getBlock(dx, dy, dz);
						if (cur == blk) continue;
						if (blk != AIR) need[blk & 0xFF]++;
						if (cur != AIR) repl[cur & 0xFF]++;
					}
			if (!commitInventory(need, repl)) return;
		}
		n = 0;
		for (long a = 0; a < sx; a++)
			for (long b = 0; b < sy; b++)
				for (long c = 0; c < sz; c++) {
					byte blk = buf[n++];
					long dx = ox + a, dy = oy + b, dz = oz + c;
					if (blk != AIR && inPlayerBlocks(pm, dx, dy, dz)) continue;
					setBlock(dx, dy, dz, blk);
				}
		chunkDirty = true;
		say("Copied " + sx + "x" + sy + "x" + sz + " blocks (" + sx * sy * sz + " total blocks)");
	}

	private static void outline() {
		if (survival) return;
		long cx = chunkOf(x), cy = chunkOf(y), cz = chunkOf(z);
		long ax = cx * SIZE, ay = cy * SIZE, az = cz * SIZE;
		long bx = ax + SIZE - 1, by = ay + SIZE - 1, bz = az + SIZE - 1;
		byte b = hotbar[heldBlock];
		long[] xs = { ax, bx }, ys = { ay, by }, zs = { az, bz };
		for (long yy : ys)
			for (long zz : zs)
				fill(b, ax, yy, zz, bx + 1, yy + 1, zz + 1, true);
		for (long xx : xs)
			for (long zz : zs)
				fill(b, xx, ay, zz, xx + 1, by + 1, zz + 1, true);
		for (long xx : xs)
			for (long yy : ys)
				fill(b, xx, yy, az, xx + 1, yy + 1, bz + 1, true);
	}

	/** Blast resistance in the same units as explosion power. */
	private static int explosionResistance(byte block) {
		if (block == AIR || block == GLASS || isLeaves(block)) return 0;
		if (block == MAGMA ||block == BASALT) return 2;
        if (block == OBSIDIAN) return 3;
		return 1;
	}

	private static void explode(long centerX, long centerY, long centerZ, int power) {
		boom(centerX, centerY, centerZ);
		if (survival && dist(centerX, centerY, centerZ) <= power + 2) damage(1);
		final int r2 = power * power;
		Deque<long[]> stack = new ArrayDeque<>();
		stack.push(new long[] { centerX, centerY, centerZ });
		Set<Long> detonated = new HashSet<>();
		while (!stack.isEmpty()) {
			long[] c = stack.pop();
			if (!detonated.add((c[0] * 31 + c[1]) * 31 + c[2])) continue;
			for (int dx = -power; dx <= power; dx++) {
				int remX = r2 - dx * dx;
				for (int dy = -power; dy <= power; dy++) {
					int remY = remX - dy * dy;
					if (remY < 0) continue;
					long bx = c[0] + dx, by = c[1] + dy;
					long zLo = c[2] - (int) Math.sqrt(remY), zHi = c[2] + (int) Math.sqrt(remY);
					for (long bz = zLo; bz <= zHi; ) {
						long segEnd = Math.min(zHi, bz | MASK);
						Octree ch = world.chunk(bx >> SHIFT, by >> SHIFT, bz >> SHIFT);
						if (ch == null || ch == World.UNLOADED) { bz = segEnd + 1; continue; }
						for (; bz <= segEnd; bz++) {
							byte block = ch.get((byte) (bx & MASK), (byte) (by & MASK), (byte) (bz & MASK));
							if (block == AIR) continue;
							// Remaining blast energy falls off with distance; resistance 0 is always vulnerable.
							double energy = power - Math.sqrt(dx * dx + dy * dy + (bz - c[2]) * (double) (bz - c[2]));
							if (energy <= explosionResistance(block)) continue;
							setBlock(bx, by, bz, AIR);
							Particles.debris(bx, by, bz, block, c[0], c[1], c[2]);
							if (block == DYNAMITE) stack.push(new long[] { bx, by, bz });
						}
					}
				}
			}
		}
	}

	/** Mode 1 = only into air (leaves, logs, ice, gems), mode 2 = only over leaves (the holes punched in a canopy). */
	private static void defer(long chunkKey, long x, long y, long z, byte block) {
		if (pendingCount > PENDING_MAX) trimPending();
		long idx = (x & MASK) | ((y & MASK) << SHIFT) | ((z & MASK) << 2 * SHIFT);
		long mode = block == AIR ? 2 : 1;
		long entry = idx | (mode << 18) | ((long) (block & 0xFF) << 20);
		if (pendingWrites.computeIfAbsent(chunkKey, k -> new LinkedHashSet<>()).add(entry))
			pendingCount++;
	}

	/** Replays feature writes that earlier chunks made into this freshly generated one. Main thread only. */
	static void applyPending(long cx, long cy, long cz) {
		long key = World.key(cx, cy, cz);
		Set<Long> ops = pendingWrites.get(key);
		if (ops == null)
			return;
		boolean g = generating;
		long h = homeKey;
		generating = true;
		homeKey = key; // so these writes aren't recorded again
		try {
			for (long e : ops) {
				int idx = (int) (e & 0x3FFFF), mode = (int) ((e >> 18) & 3);
				byte blk = (byte) (e >> 20);
				long x = cx * SIZE + (idx & MASK), y = cy * SIZE + ((idx >> SHIFT) & MASK), z = cz * SIZE + ((idx >> 2 * SHIFT) & MASK);
				byte cur = getBlock(x, y, z);
				if (mode == 1 ? cur == AIR : isLeaves(cur))
					setBlock(x, y, z, blk);
			}
		} finally {
			generating = g;
			homeKey = h;
			if (pendingWrites.remove(key) != null) pendingCount = Math.max(0, pendingCount - ops.size());
		}
	}

	private static void click(int button) {
		if (dead) return;
		final long hx = hoveredX, hy = hoveredY, hz = hoveredZ;
		final boolean has = hy != NO_POS;
		final boolean emptyHand = hotbar[heldBlock] == AIR;      // captured first: placing your last block must not trigger the dynamite/emerald code below
		if (fill) {
			if (has) {
				if (button == 1) { x0 = hx; y0 = hy; z0 = hz; }
				else if (button == 3) { x1 = hx; y1 = hy; z1 = hz; }
			}
		} else if (has) {
			if (button == 1) {
				if (!survival) {                                 // survival breaking is hold-to-break, see survivalBreakTick()
					block(getBlock(hx, hy, hz), 0, hx, hy, hz);
					Particles.burst(hx, hy, hz, getBlock(hx, hy, hz), 14, 0.04);
					setBlock(hx, hy, hz, AIR);
				}
			} else if (button == 3 && !(survival && emptyHand)) {
				long px = hx + dirX, py = hy + dirY, pz = hz + dirZ;
				byte placed = hotbar[heldBlock];
				if (placed == AIR || !intersectsPlayer(px, py, pz)) {
					setBlock(px, py, pz, placed);
					block(placed, 1, px, py, pz);
					if (survival) consumeHeld();
					hoveredX = newHoverX = px;
					hoveredY = newHoverY = py;
					hoveredZ = newHoverZ = pz;
					dirX = newDirX = -dirX;
					dirY = newDirY = -dirY;
					dirZ = newDirZ = -dirZ;
					hoveredType = getType(placed);
					chunkDirty = true;
				}
			}
		}
		if (button == 3 && has && emptyHand) {
			byte b = getBlock(hx, hy, hz);
			if (b == DYNAMITE)
				explode(hx, hy, hz, power);
			else if (b == EMERALD && !survival)
				buildTree(hx, hy + 1, hz, 5, new Random());
		}
	}

	private static void pick() {
		if (hoveredY == NO_POS) return;
		byte id = getBlock(hoveredX, hoveredY, hoveredZ);
		if (id == AIR) return;
		if (survival) { // only selects something you already own
			for (int p = 0; p < INV_PAGES; p++)
				for (int i = 0; i < INV_SLOTS; i++)
					if (invId[p][i] == id) { page = p; heldBlock = (byte) i; return; }
			return;
		}
		if (xor) {
			for (byte i = 0; i < XOR_PAGE.length; i++)
				if (XOR_PAGE[i] == id) { heldBlock = i; return; }
			return;
		}
		for (byte p = 0; p < PAGES.length; p++)
			for (byte i = 0; i < PAGES[p].length; i++)
				if (PAGES[p][i] == id) { page = p; heldBlock = i; return; }
	}

	// ------------------------------------------------------------------ textures

	private static void textures() {
		Random rand = new Random(7817105610522912629L);
		for (byte type = 1; type < BLOCK_COUNT; type++) {
			int gsd_tempA = 0;
			for (byte y = 0; y < 48; y++) {
				for (byte x = 0; x < 16; x++) {
					int pattern, gsd_final, tint;
					if (xor) {
						if (type == GRASS || type == EMERALD) {
							pattern = (x ^ y) * 16 + 1;
							pattern = pattern << 8;
						} else if (type == DIRT || type == TOPAZ || type == SAND || type == YELLOW_LEAVES || type == MAGMA) {
							pattern = (x ^ y) * 16 + 1;
							pattern = pattern << 16 | pattern << 8;
						} else if (type == STONE || type == TANZANITE) {
							pattern = (x ^ y) * 16 + 1;
						} else if (type == BRICKS || type == DYNAMITE || type == RED_LEAVES || type == RUBY) {
							pattern = (x ^ y) * 16 + 1;
							pattern = pattern << 16;
						} else if (type == OAK_LOG || type == ICE || type == OAK_PLANKS || type == DIAMOND) {
							pattern = (x ^ y) * 16 + 1;
							pattern |= pattern << 8;
						} else if (type == LEAVES || type == RHODONITE) {
							pattern = (x ^ y) * 16 + 1;
							pattern |= pattern << 16;
						} else if (type == MARBLE) {
							pattern = 0xE8E5DD;
						} else if (type == GLASS || type == SNOW || type == BIRCH_LOG || type == BIRCH_PLANKS || type == QUARTZ) {
							pattern = (x ^ y) * 16 + 1;
							pattern |= pattern << 16 | pattern << 8;
						} else if (type == SLATE || type == SAPPHIRE) {
							pattern = (x & y) * 16 + 1;
						} else if (type == AUTUMN_GRASS) {
							pattern = (x & y) * 16 + 1;
							pattern = pattern << 16 | pattern << 8;
						} else if (type == ORANGE_LEAVES) {
							pattern = (x & y) * 16 + 1;
							pattern = pattern << 16;
						} else if (type == ASH) {
							pattern = (x & y) * 16 + 1;
							pattern |= pattern << 16 | pattern << 8;
						} else if (type == AMETHYST) {
							pattern = (x & y) * 16 + 1;
							pattern |= pattern << 16;
						} else {
							pattern = ((x & 15) * 16 << 16 | (y & 15) * 16 + (x & 15) * 16 | (y & 15) * 16 << 8) + 1;
						}
					} else {
						double pNoise = texNoise(x, y);
						if (type != STONE || rand.nextInt(2) == 1) gsd_tempA = 0xFF - rand.nextInt(0x60);
						tint = 0x966C4A;
						switch (type) {
						case STONE:
							tint = 0x7F7F7F;
							break;
						case GRASS: case AUTUMN_GRASS: {
							int edge = (((x * x * 3 + x * 81) / 2) & 3) + 18;
							if (y < edge)
								tint = type == AUTUMN_GRASS ? 0xFF8A1A : 0x7AFF40;
							else if (y < edge + 1)
								gsd_tempA = gsd_tempA * 1 / 3;
							break;
						}
						case OAK_LOG:
							tint = 0x776644;
							byte wood = 7;
							int dx = x - wood;
							int dy = (y & 15) - wood;
							if (dx < 0) dx = 1 - dx;
							if (dy < 0) dy = 1 - dy;
							if (dy > dx) dx = dy;
							double center = (Math.sqrt(dx * dx + dy * dy) * 0.25 + Math.max(dx, dy) * 0.75);
							if (y < 16 || y > 32) {
								if (center < 8) {
									tint = 0xCCAA77;
									gsd_tempA = 196 - (int) rand.nextInt(32) + dx % 3 * 32;
								} else if (dx > dy) {
									gsd_tempA = (int) (texNoise(y, x * 0.25) * 255 * (180 - Math.sin(x * Math.PI) * 50) / 100);
								} else {
									gsd_tempA = (int) (texNoise(x, y * 0.25) * 255 * (180 - Math.sin(x * Math.PI) * 50) / 100);
								}
							} else {
								gsd_tempA = (int) (texNoise(x, y * 0.25) * 255 * (180 - Math.sin(x * Math.PI) * 50) / 100);
							}
							break;
						case BRICKS:
							tint = 0xB53A15;
							if ((x + y / 4 * 4) % 8 == 0 || y % 4 == 0)
								tint = 0xBCAFA5;
							break;
						case SLATE:
							tint = 0x4F4F4F;
							double bDX = Math.abs(x % 8 - 4);
							double bDY = Math.abs((y % 4) - 2) * 2;
							if (y / 4 % 2 == 1)
								bDX = Math.abs((x + 4) % 8 - 4);
							double b = Math.sqrt(bDX * bDX + bDY * bDY) * 0.5 + Math.max(bDX, bDY) * 0.5;
							if (b > 4)
								tint = 0x7F7F7F;
							break;
						case DYNAMITE:
							tint = (x ^ y) * 16;
							tint = ~(tint << 8 | tint);
							break;
						case SNOW:
							tint = 0xFFFFFF;
							break;
						case MARBLE: {
							double broad = texNoise(x * 0.19 + 3.2, y * 0.19 - 7.1);
							double medium = texNoise(x * 0.57 - 13.0, y * 0.57 + 5.0);
							double grain = texNoise(x * 1.13 + 17.0, y * 1.13 - 9.0);
							double fine = texNoise(x * 2.35 - 4.0, y * 2.35 + 23.0);
							double fleck = hash3(x, y, MARBLE, 0x71A);
							double variation = 0.58 + broad * 0.34 + medium * 0.22 + grain * 0.16 + fine * 0.10;
							int q = shade(0xE9E6DF, variation);
							double veinField = Math.abs((x + y * 0.41 + (medium - 0.5) * 10.0 + (broad - 0.5) * 6.0) % 15.0);
							if (veinField < 1.1 + grain * 1.1) q = shade(q, 0.72 + medium * 0.16);
							else if (veinField < 2.4 && fine > 0.42) q = shade(q, 1.08 + fine * 0.08);
							if (fleck > 0.965) q = shade(q, 0.84);
							else if (fleck < 0.035) q = shade(q, 1.06);
							tint = q;
							gsd_tempA = 0xFF;
							break;
						}
						case MAGMA:
							tint = 0xFF9F00;
							bDX = Math.abs(x % 8 - 4);
							bDY = Math.abs((y % 4) - 2) * 2;
							if (y / 4 % 2 == 1)
								bDX = Math.abs((x + 4) % 8 - 4);
							b = Math.sqrt(bDX * bDX + bDY * bDY) * 0.5 + Math.max(bDX, bDY) * 0.5;
							if (b > 4)
								tint = 0xFF6F00;
							break;
						case SAND:
							tint = 0xFFFF9F;
							break;
						case ICE:
							tint = (x ^ y) * 16;
							tint = ~(tint << 16);
							break;
						case TOPAZ:
							tint = ~((x ^ y) * 16);
							break;
						case EMERALD:
							tint = (x ^ y) * 16;
							tint = ~(tint << 16 | tint);
							break;
						case TANZANITE:
							tint = (x ^ y) * 16;
							tint = ~(tint << 16 | tint << 8);
							break;
						case RHODONITE:
							tint = (x ^ y) * 16;
							tint = ~(tint << 8);
							break;
						case OAK_PLANKS: case BIRCH_PLANKS:
							tint = plankTint(type, x, y);
							gsd_tempA = softShade(gsd_tempA, 6);
							break;
						case BIRCH_LOG:
							tint = birchTint(x, y);
							gsd_tempA = 0xFF;
							break;
						case TILE:
							tint = triangleTint(x, y);
							break;
						default:
							if ((type >= RUBY && type <= MARBLE) || type == GOLD || type == GOLD_ORE || type == DIAMOND || type == QUARTZ) {
								tint = extraTint(type, x, y);
								if (X_STYLE[xStyleIndex(type)] == 4)
									gsd_tempA = 0xFF;
							}
							break;
						}
						gsd_final = gsd_tempA;
						if (y >= 32)
							gsd_final /= 2;
						if (isLeaves(type))
							tint = leafTint(type, x, y, pNoise);
						if (type == GLASS) {
							byte sizeX = 16, sizeY = 16;
							double localX = x & 15;
							double localY = y & 15;
							boolean border = localX < 1 || localX > 14 || localY < 1 || localY > 14;
							double[][] lines = {{sizeX / 3 - 2, 2 * sizeY / 3 - 2, sizeX / 3 + 2, 2 * sizeY / 3 + 2}, {2 * sizeX / 3 - 2, sizeY / 4 - 2, 2 * sizeX / 3 + 2, sizeY / 4 + 2}};
							boolean diagonal = false;
							for (double[] line : lines) {
								double startX = line[0], startY = line[1], endX = line[2], endY = line[3];
								if (localX >= Math.min(startX, endX) && localX <= Math.max(startX, endX) && localY >= Math.min(startY, endY) && localY <= Math.max(startY, endY)) {
									double dx = endX - startX, dy = endY - startY;
									double t = ((localX - startX) * dx + (localY - startY) * dy) / (dx * dx + dy * dy);
									if (t >= 0 && t <= 1) {
										double closestX = startX + t * dx;
										double closestY = startY + t * dy;
										if (Math.hypot(localX - closestX, localY - closestY) < 0.5) {
											diagonal = true;
											break;
										}
									}
								}
							}
							tint = (border || diagonal) ? 0xFFFFFF : 0;
						}
						int col = ((tint & 0xFFFFFF) == 0 ? 0 : 0xFF) << 24 | (tint >> 16 & 0xFF) * gsd_final / 0xFF << 16 | (tint >> 8 & 0xFF) * gsd_final / 0xFF << 8 | (tint & 0xFF) * gsd_final / 0xFF;
						atlas[x + y * 16 + type * 768] = col;
						continue;
					}
					int r = (pattern >> 16) & 0xFF;
					int g = (pattern >> 8) & 0xFF;
					int b = pattern & 0xFF;
					int color = (0xFF << 24) | (r << 16) | (g << 8) | b;
					atlas[x + y * 16 + type * 768] = color;
				}
			}
		}
		computeOpaque();
	}

	/** A block is "opaque" if none of its 768 atlas texels is transparent: a shadow ray that enters it always stops. */
	static void computeOpaque() {
		boolean[] o = new boolean[256];
		for (byte id = 1; id < BLOCK_COUNT; id++) {
			boolean all = true;
			for (int i = 0; i < 768 && all; i++)
				if ((atlas[id * 768 + i] & 0xFFFFFF) == 0)
					all = false;
			o[id] = all;
		}
		OPAQUE = o;
	}

	private static int triangleTint(int x, int y) {
		double u = Math.abs((x & 15) - 7.5), v = Math.abs((y & 15) - 7.5);
		return u > v ? 0x141414 : 0xC81E1E;
	}

	/** Scales down the per-pixel brightness noise: strength 16 = original, 0 = flat. */
	private static int softShade(int noisy, int strength) {
		return 255 - (((255 - noisy) * strength) >> 4);
	}

	/** Planks (oak + birch): 4 boards per face, visible horizontal grain, dark seams, staggered joints. */
	private static int plankTint(int type, int x, int y) {
		boolean birch = type == BIRCH_PLANKS;
		int base  = birch ? 0xD9C48F : 0xCBA976;
		int seam  = birch ? 0xA89260 : 0xA08350;
		int joint = birch ? 0xC0AB76 : 0xB59660;
		int lx = x & 15, ly = y & 15, board = ly >> 2;
		if ((ly & 3) == 3)
			return seam;
		int jx = (board * 7 + 3) & 15;
		if (lx == jx)
			return joint;
		double tone = 0.93 + 0.12 * hash3(board, lx > jx ? 1 : 0, type, 0x9A1);
		// Long streaks along the board: stretched in x, sharp in y.
		double streak = texNoise(lx * 0.15 + board * 3.1, ly * 1.6 + 0.5);
		// A bit of per-pixel grit on top.
		double grit = hash3(lx, ly, type, 0x9A2);
		double f = tone * (0.84 + 0.22 * streak + 0.08 * grit);
		// Occasional dark grain line
		if (hash3(lx >> 2, ly, type, 0x9A3) < 0.12)
			f *= 0.9;
		return shade(base, f);
	}

	// ---- Birch side marks: edit the seed to reroll the whole layout ----
	static final double BIRCH_SPECKLE = 0.07;   // chance of a grey fleck on a bare pixel
	static final int BIRCH_MARKS_PER_BAND = 2;  // dashes per 4-row band
	static final byte[] BIRCH_MARKS = buildBirchMarks(3);

	/** 16x16 mask: 0 = bark, 1 = main dash, 2 = dash pixel above/below, 3 = grey speckle. */
	static byte[] buildBirchMarks(long seed) {
		Random rng = new Random(seed);
		byte[] m = new byte[16 * 16];
		int slot = 16 / BIRCH_MARKS_PER_BAND;
		for (int band = 0; band < 4; band++)
			for (int k = 0; k < BIRCH_MARKS_PER_BAND; k++) {
				int start = (k * slot + (band & 1) * (slot / 2) + rng.nextInt(2)) & 15;
				int len = 2 + rng.nextInt(4);            // 2..5 px wide
				int r0 = 1 + rng.nextInt(2);             // row 1 or 2 of the band
				int above = rng.nextInt(len);            // column of the pixel above
				int bw = len >= 3 ? len - 2 : 1;         // shorter row below, centered
				int off = len >= 3 ? 1 : 0;
				int y = band * 4 + r0;
				for (int i = 0; i < len; i++)
					m[y * 16 + ((start + i) & 15)] = 1;
				m[(y - 1) * 16 + ((start + above) & 15)] = 2;
				for (int i = 0; i < bw; i++)
					m[(y + 1) * 16 + ((start + off + i) & 15)] = 2;
			}
		for (int i = 0; i < m.length; i++)
			if (m[i] == 0 && rng.nextDouble() < BIRCH_SPECKLE)
				m[i] = 3;
		return m;
	}

	/** Birch log: white bark with evenly spread dark dashes on the sides, oak-style ringed end grain on top/bottom. */
	private static int birchTint(int x, int y) {
		int lx = x & 15, ly = y & 15;
		if (y < 16 || y >= 32)
			return birchEnd(lx, ly);
		return birchSide(lx, ly);
	}

	/** Same geometry as the oak log's end grain: square-ish rings, bark outside, wood inside. */
	private static int birchEnd(int lx, int ly) {
		int dx = lx - 7, dy = ly - 7;
		if (dx < 0) dx = 1 - dx;
		if (dy < 0) dy = 1 - dy;
		int m = Math.max(dx, dy);
		double center = Math.sqrt(m * m + (double) Math.min(dx, dy) * Math.min(dx, dy)) * 0.25 + m * 0.75;
		if (center < 8) {
			int br = 196 - (int) (hash3(lx, ly, 0, 0xB20) * 32) + (m % 3) * 32;
			return shade(0xE6D4A4, Math.min(1.0, br / 255.0) * 1.05);
		}
		if (hash3(lx, ly, 1, 0xB21) < 0.08)
			return 0x4A4845;
		return shade(0xE9E6DC, 0.7 + 0.3 * texNoise(lx * 0.5, ly * 0.5) + 0.1 * hash3(lx, ly, 2, 0xB22));
	}

	private static int birchSide(int lx, int ly) {
		switch (BIRCH_MARKS[(ly & 15) * 16 + (lx & 15)]) {
		case 1: return 0x2E2C2A;
		case 2: return 0x3A3835;
		case 3: return 0xBDBAB0;
		}
		// Vertical streaks like the oak log's side grain (stretched in y, sharp in x)
		double streak = texNoise(lx * 1.5 + 3.7, ly * 0.25);
		double grit = hash3(lx, ly, 1, 0xB36);
		return shade(0xE9E6DC, 0.68 + 0.35 * streak + 0.08 * grit);
	}

	private static int xStyleIndex(byte type) {
		if (type == GOLD) return 20;
		if (type == GOLD_ORE) return 21;
		if (type == DIAMOND) return 22;
		if (type == QUARTZ) return 23;
		return type - RUBY;
	}

	private static int extraTint(byte type, byte x, byte y) {
		int lx = x & 15, ly = y & 15;
		int i = xStyleIndex(type), base = X_BASE[i], acc = X_ACCENT[i];
		switch (X_STYLE[i]) {
		case 1: {
			int h = lx * 374761393 + ly * 668265263 + type * 362437;
			h = (h ^ (h >>> 13)) * 1274126177;
			h ^= h >>> 16;
			return (h & 15) < 3 ? acc : base;
		}
		case 2: return (ly % 4 == 0 || (lx + (ly / 4 % 2) * 8) % 16 == 0) ? acc : base;
		case 3: return (lx % 8 == 0 || ly % 8 == 0) ? acc : base;
		case 4: return gemTint(base, acc, lx, ly);
		case 5: return (((lx >> 3) ^ (ly >> 3)) & 1) == 0 ? base : acc;
		default: return base;
		}
	}

	private static final double[] GEM_SECTOR = { 0.75, 1.10, 0.55, 1.28 }; // right, left, bottom, top facet (light from top-left)
	private static final double[] GEM_RING = { 1.15, 1.0, 0.85 };          // table, crown, rim

	private static int gemTint(int base, int acc, int lx, int ly) {
		double u = lx - 7.5, v = ly - 7.5;
		double au = Math.abs(u), av = Math.abs(v), m = Math.max(au, av);
		int ring = Math.min(2, (int) (m / 2.7));
		int sector = au > av ? (u > 0 ? 0 : 1) : (v > 0 ? 2 : 3);
		double frac = m - ring * 2.7;
		boolean edge = m > 6.9                            // outer outline
				|| (ring > 0 && frac < 0.7)               // ring borders
				|| (ring > 0 && Math.abs(au - av) < 0.7); // diagonal facet borders
		if (edge)
			return acc;
		if (m < 1.0)
			return shade(base, 1.75);
		return shade(base, GEM_SECTOR[sector] * GEM_RING[ring]);
	}

	/** f < 1 darkens, f > 1 pushes toward white. */
	private static int shade(int c, double f) {
		int r = c >> 16 & 0xFF, g = c >> 8 & 0xFF, b = c & 0xFF;
		if (f <= 1) {
			r *= f; g *= f; b *= f;
		} else {
			double k = f - 1;
			r += (255 - r) * k; g += (255 - g) * k; b += (255 - b) * k;
		}
		return Math.min(255, r) << 16 | Math.min(255, g) << 8 | Math.min(255, b);
	}

	// ------------------------------------------------------------------ GUI

	private int gy, lineH;

	private void ln(Graphics2D g, String s) {
		g.drawString(s, 3, gy);
		gy += lineH;
	}

	private static String format(double value, DecimalFormat f) {
		if (Math.abs(value) >= 1E10 || Double.isNaN(value))
			return String.valueOf(value);
		return f.format(value);
	}

	static String posStr(long a, long b, long c) {
		return b == NO_POS ? "unset" : "(" + a + ", " + -b + ", " + c + ")";
	}

	private static final Map<Long, Font> FONTS = new ConcurrentHashMap<>();
	static Font pal(int style, int size) {
		return FONTS.computeIfAbsent(((long) style << 32) | size, k -> new Font("Palatino Linotype", style, size));
	}

	private static long ramStamp;
	private static String ramText = "";
	/** Re-reads the heap numbers twice a second instead of every frame. */
	private static String ramText() {
		long n = System.currentTimeMillis();
		if (n - ramStamp > 500) {
			ramStamp = n;
			Runtime rt = Runtime.getRuntime();
			ramText = String.format(Locale.ROOT, "RAM Used: %.1fMB", (rt.totalMemory() - rt.freeMemory()) / 1048576.0);
		}
		return ramText;
	}

	private void drawHotbar(Graphics2D g2d, byte[] hb, int sc) {
		int slot = 40 * sc, padding = 2 * sc;
		int hotbarX = width / 2 - (slot * hb.length) / 2;
		int hotbarY = height - slot - 10;
		g2d.setColor(HOTBAR_BG);
		g2d.fillRect(hotbarX - 2 * sc, hotbarY - 2 * sc, slot * hb.length + 4 * sc, slot + 4 * sc);
		g2d.setColor(HOTBAR_BORDER);
		g2d.drawRect(hotbarX - 2 * sc, hotbarY - 2 * sc, slot * hb.length + 4 * sc, slot + 4 * sc);
		for (int i = 0; i < hb.length; i++) {
			g2d.drawImage(atlasImg,
					hotbarX + i * slot + padding, hotbarY + padding,
					hotbarX + i * slot + slot - padding, hotbarY + slot - padding,
					0, 16 * (hb[i] * 3 + 1), 16, 16 * (hb[i] * 3 + 2), null);
		}
		if (survival) drawSlotCounts(g2d, hotbarX, hotbarY, slot, padding, sc);
		g2d.setColor(Color.white);
		g2d.setStroke(hotbarStroke);
		g2d.drawRect(hotbarX + heldBlock * slot, hotbarY, slot, slot);
		if (survival) {
			int barH = slot / 4, barTop = hotbarY - 4 * sc - barH;
			drawHealth(g2d, hotbarX - 2 * sc, barTop, slot * hb.length + 4 * sc, barH, sc);
		}
	}

	/** Stack counts: right-aligned to the slot's icon and clipped to it, so big numbers grow leftwards and never touch neighbours. */
	private static void drawSlotCounts(Graphics2D g2d, int hotbarX, int hotbarY, int slot, int padding, int sc) {
		int[] cnt = invCount[page % INV_PAGES];
		g2d.setFont(pal(Font.BOLD, countFontSize * sc));
		FontMetrics fm = g2d.getFontMetrics();
		Shape oldClip = g2d.getClip();
		for (int i = 0; i < INV_SLOTS; i++) {
			if (cnt[i] <= 1) continue;
			String s = Integer.toString(cnt[i]);
			int sx = hotbarX + i * slot;
			int tx = sx + slot - padding - 2 * sc - fm.stringWidth(s), baseline = hotbarY + slot - padding - 2 * sc;
			g2d.setClip(sx + padding, hotbarY + padding, slot - 2 * padding, slot - 2 * padding);
			g2d.setColor(Color.BLACK); g2d.drawString(s, tx + sc, baseline + sc);
			g2d.setColor(Color.WHITE); g2d.drawString(s, tx, baseline);
		}
		g2d.setClip(oldClip);
	}

	private static final Color HP_FULL = new Color(200, 30, 40), HP_EMPTY = new Color(18, 18, 20);

	private static void drawHealth(Graphics2D g, int x, int y, int w, int h, int sc) {
		g.setColor(new Color(30, 30, 30, 200)); g.fillRect(x, y, w, h);
		final int c = Math.max(2, h / 4);
		final long left = flashUntil - System.currentTimeMillis();
		final int fFrom = flashFrom, fTo = flashTo;
		for (int i = 0; i < MAX_HEALTH; i++) {
			int x0 = x + i * w / MAX_HEALTH, x1 = x + (i + 1) * w / MAX_HEALTH;
			boolean full = i < health;
			if (full) g.setColor(HP_FULL);
			else if (left > 0 && i >= fFrom && i < fTo) { // just lost: light gray, fading to black over the last 100 ms
				float t = Math.min(1f, left / 100f);
				int v = 18 + (int) ((205 - 18) * t);
				g.setColor(new Color(v, v, v));
			} else g.setColor(HP_EMPTY);
			g.fillRect(x0, y, x1 - x0, h);
			g.setColor(new Color(150, 150, 150, full ? 90 : 60));
			g.fillRect(x0, y, c, c); g.fillRect(x1 - c, y, c, c);
			g.fillRect(x0, y + h - c, c, c); g.fillRect(x1 - c, y + h - c, c, c);
		}
		g.setColor(Color.GRAY);
		int lw = Math.max(1, sc);
		for (int i = 1; i < MAX_HEALTH; i++) g.fillRect(x + i * w / MAX_HEALTH - lw / 2, y, lw, h);
		g.setColor(HOTBAR_BORDER); g.drawRect(x, y, w, h);
	}

	private static void updateHudSnapshot() {
	    SplitDecimal[] cur = hudPos;
	    if (cur[0].equals(x) && cur[1].equals(y) && cur[2].equals(z)) return;
	    hudPos = new SplitDecimal[] { copyOf(x), copyOf(y), copyOf(z) };
	}

	private void gui(Graphics2D g2d) {
		byte[] hb = hotbar;
		int sc = scale;
		if (guiFont == null || guiFontScale != sc) {
			guiFont = pal(1, 16 * sc);
			guiFontScale = sc;
			hotbarStroke = new BasicStroke(3 * sc);
		}
		lineH = 18 * sc;
		gy = 16 * sc;
		drawHotbar(g2d, hb, sc);
		g2d.setFont(guiFont);
		if (option == 0 && guiEnabled) {
			if (showFPS) {
				g2d.setColor(Color.red);
				if (vSync) {
					ln(g2d, fps + " FPS (VSync)");
				} else {
					ln(g2d, fps + " FPS");
				}
			}
			if (showXYZ) {
				SplitDecimal[] p = hudPos;
				g2d.setColor(Color.yellow);
				ln(g2d, "X: " + SplitDecimal.fmt3(p[0], false));
				ln(g2d, "Y: " + SplitDecimal.fmt3(p[1], true));
				ln(g2d, "Z: " + SplitDecimal.fmt3(p[2], false));
			}
			if (showRot) {
				SplitDecimal[] p = hudPos;
				long fx = floorOf(p[0]), fy = -floorOf(p[1]), fz = floorOf(p[2]);
				g2d.setColor(Color.green);
				ln(g2d, "Chunk: (" + (fx >> SHIFT) + ", " + (fy >> SHIFT) + ", " + (fz >> SHIFT) + ")");
				ln(g2d, "Index: (" + (fx & MASK) + ", " + (fy & MASK) + ", " + (fz & MASK) + ")");
				if (degrees)
					ln(g2d, "Rotation: (" + format(yaw * (180 / Math.PI), FMT1) + ", " + format(pitch * (180 / Math.PI), FMT1) + ")");
				else
					ln(g2d, "Rotation: (" + format(yaw, FMT3) + ", " + format(pitch, FMT3) + ")");
			}
			if (showCyan) {
				g2d.setColor(Color.cyan);
				ln(g2d, "Time: " + time);
				ln(g2d, "Render Distance: " + dist + " (" + radius + ")");
			}
			if (showMagenta) {
				g2d.setColor(Color.magenta);
				ln(g2d, "Window Size: " + width + "x" + height + " (" + resX + "x" + resY + ", 1/" + (1 << 2 * (3 - detail)) + ")");
				String mode = classic && xor ? "Retro" : xor ? "Bitwise" : classic ? "Classic" : "Complex";
				ln(g2d, "Render Mode: " + mode);
			}
			if (showExtra) {
				g2d.setColor(Color.white);
				ln(g2d, "Hotbar Page: " + (page + 1) + "/" + pageCount() + " (particles: " + Particles.count + ")");
				ln(g2d, ramText());
				if (fly)
					ln(g2d, "Flight enabled!");
				if (hoveredY != NO_POS)
					ln(g2d, "Looking at " + posStr(hoveredX, hoveredY, hoveredZ) + " : " + hoveredType);
				if (fill) {
					ln(g2d, "Fill mode active!");
					ln(g2d, "Block A: " + posStr(x0, y0, z0));
					ln(g2d, "Block B: " + posStr(x1, y1, z1));
					ln(g2d, "Copy mode " + (copyMode ? "ON" : "OFF"));
				}
				if (System.currentTimeMillis() - locMsgTime < 5000) {
					g2d.setColor(new Color(255, 127, 0));
					ln(g2d, locMsg);
				}
			}
		} else if (option == 2 && controlsUIEnabled) {
			g2d.setColor(Color.white);
			ln(g2d, "Bitwise Nexus " + VERSION + ", made on October 28, 2026");
			g2d.setColor(Color.red);
			ln(g2d, "Interface controls: F1 to hide all, F3 toggles HUD, F4 toggles controls HUD");
			g2d.setColor(Color.yellow);
			ln(g2d, "Original code from TheSunCat's Minecraft4k-Reversed, heavily modified by hypernebulae!");
			g2d.setColor(Color.green);
			ln(g2d, "Move: WASD");
			ln(g2d, "Jump: Space - Sprint: Ctrl");
			ln(g2d, "Move Camera: Arrow Keys - Mouse");
			ln(g2d, "Break Block: Left Click - Place Block: Right Click");
			ln(g2d, "Pick Block: Middle Click");
			g2d.setColor(Color.cyan);
			ln(g2d, "Enable Flight: F");
			ln(g2d, "Change Block Type: [1-" + hb.length + "] or Scroll Wheel");
			ln(g2d, "Change Pixel Scale: P+ / M-");
			ln(g2d, "Toggle Display Debug: F5+[1-6] - U to reset");
			ln(g2d, "Take Screenshot: F2");
			ln(g2d, "Toggle VSync: F6");
			ln(g2d, "Toggle Fullscreen: F11");
			ln(g2d, "Reset Rotation: T");
			g2d.setColor(Color.magenta);
			ln(g2d, "Switch Hotbar: Q/E");
			ln(g2d, "Fill Mode: F7; Left/Right Click to set Block A/B; F8 to execute, places held block");
			ln(g2d, "Copy Mode: C to toggle while Fill Mode is on");
			ln(g2d, "Spawn Chunk Outline: G");
			ln(g2d, "Open Teleport Menu: F10");
			ln(g2d, "Change Lighting: L");
			ln(g2d, "Locate Feature: N to cycle target, B to teleport");
		}
	}

	private static Color pickFogColor(Color initial) {
		final int s = Math.max(1, scale);
		final int[] rgb = { initial.getRed(), initial.getGreen(), initial.getBlue() };
		final boolean[] ok = { false };
		final JDialog dlg = new JDialog(frame, "Fog RGB Color", true);
		final JTextField hex = new JTextField(7);
		hex.setFont(pal(Font.PLAIN, 14 * s));
		hex.setText(String.format(Locale.ROOT, "%02X%02X%02X", rgb[0], rgb[1], rgb[2]));

		final int rowH = 40 * s, trackX = 36 * s, rightPad = 64 * s;
		final Color[] chan = { new Color(255, 70, 70), new Color(70, 220, 90), new Color(80, 130, 255) };
		final String[] names = { "R", "G", "B" };

		final JPanel panel = new JPanel() {
			int active = -1;
			{
				setPreferredSize(new Dimension(420 * s, 3 * rowH + 80 * s));
				setBackground(new Color(40, 40, 44));
				MouseAdapter ma = new MouseAdapter() {
					@Override public void mousePressed(MouseEvent e) {
						int row = e.getY() / rowH;
						active = row >= 0 && row < 3 ? row : -1;
						drag(e);
					}
					@Override public void mouseDragged(MouseEvent e) { drag(e); }
					@Override public void mouseReleased(MouseEvent e) { active = -1; }
					void drag(MouseEvent e) {
						if (active < 0) return;
						double t = (e.getX() - trackX) / (double) (getWidth() - trackX - rightPad);
						rgb[active] = (int) Math.round(Math.max(0, Math.min(1, t)) * 255);
						hex.setText(String.format(Locale.ROOT, "%02X%02X%02X", rgb[0], rgb[1], rgb[2]));
						repaint();
					}
				};
				addMouseListener(ma);
				addMouseMotionListener(ma);
			}
			@Override protected void paintComponent(Graphics g0) {
				super.paintComponent(g0);
				Graphics2D g = (Graphics2D) g0;
				g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
				g.setFont(pal(Font.BOLD, 15 * s));
				FontMetrics fm = g.getFontMetrics();
				int trackW = getWidth() - trackX - rightPad, th = 8 * s;
				for (int i = 0; i < 3; i++) {
					int cy = i * rowH + rowH / 2;
					g.setColor(Color.WHITE);
					g.drawString(names[i], 12 * s, cy + (fm.getAscent() - fm.getDescent()) / 2);
					g.setPaint(new GradientPaint(trackX, 0, Color.BLACK, trackX + trackW, 0, chan[i]));
					g.fillRoundRect(trackX, cy - th / 2, trackW, th, th, th);
					g.setPaint(null);
					g.setColor(new Color(130, 130, 140));
					g.drawRoundRect(trackX, cy - th / 2, trackW, th, th, th);
					int px = trackX + (int) Math.round(rgb[i] / 255.0 * trackW), r = 8 * s;
					g.setColor(Color.WHITE);
					g.fillOval(px - r, cy - r, 2 * r, 2 * r);
					g.setColor(Color.WHITE);
					g.drawString(Integer.toString(rgb[i]), trackX + trackW + 14 * s, cy + (fm.getAscent() - fm.getDescent()) / 2);
				}
				int sy = 3 * rowH + 10 * s;
				g.setColor(new Color(rgb[0], rgb[1], rgb[2]));
				g.fillRoundRect(12 * s, sy, getWidth() - 24 * s, 50 * s, 10 * s, 10 * s);
				g.setColor(new Color(130, 130, 140));
				g.drawRoundRect(12 * s, sy, getWidth() - 24 * s, 50 * s, 10 * s, 10 * s);
			}
		};

		hex.addKeyListener(new KeyAdapter() {
			@Override public void keyReleased(KeyEvent e) {
				String t = hex.getText().trim().replace("#", "");
				if (t.length() == 3) t = "" + t.charAt(0) + t.charAt(0) + t.charAt(1) + t.charAt(1) + t.charAt(2) + t.charAt(2);
				if (t.length() != 6) return;
				try {
					int c = Integer.parseInt(t, 16);
					rgb[0] = c >> 16 & 255; rgb[1] = c >> 8 & 255; rgb[2] = c & 255;
					panel.repaint();
				} catch (NumberFormatException ignored) {}
			}
		});

		JButton okBtn = new JButton("OK"), cancelBtn = new JButton("Cancel");
		Font bf = pal(Font.BOLD, 14 * s);
		final int nudge = 3 * s; // how far the text is pushed down
		Insets btnMargin = new Insets(6 * s + nudge, 14 * s, Math.max(0, 6 * s - nudge), 14 * s);
		okBtn.setFont(bf); cancelBtn.setFont(bf);
		okBtn.setMargin(btnMargin); cancelBtn.setMargin(btnMargin);
		okBtn.addActionListener(e -> { ok[0] = true; dlg.dispose(); });
		cancelBtn.addActionListener(e -> dlg.dispose());

		hex.setBorder(BorderFactory.createCompoundBorder(
				BorderFactory.createLineBorder(new Color(130, 130, 140)),
				BorderFactory.createEmptyBorder(3 * s + nudge, 6 * s, Math.max(0, 3 * s - nudge), 6 * s)));

		JLabel hexLabel = new JLabel("Hex: #");
		hexLabel.setFont(pal(Font.PLAIN, 14 * s));
		hexLabel.setBorder(BorderFactory.createEmptyBorder(2 * nudge, 0, 0, 0));
		JPanel south = new JPanel(new FlowLayout(FlowLayout.CENTER, 10 * s, 8 * s));
		south.add(hexLabel); south.add(hex); south.add(okBtn); south.add(cancelBtn);

		dlg.getContentPane().add(panel, BorderLayout.CENTER);
		dlg.getContentPane().add(south, BorderLayout.SOUTH);
		dlg.getRootPane().setDefaultButton(okBtn);
		dlg.pack();
		dlg.setLocationRelativeTo(frame);
		dlg.setVisible(true); // modal: returns after OK / Cancel / close
		return ok[0] ? new Color(rgb[0], rgb[1], rgb[2]) : null;
	}

	/** Same geometry as the title-screen buttons. [0] = top, [1] = below it. */
	private static Rectangle[] deathRects() {
		int gui = frontGuiScale();
		int bw = Math.min(310 * gui, Math.min(560 * gui, width - 32) - 36), bh = 42 * gui, gap = 10 * gui, bx = (width - bw) / 2;
		int stack = 3 * bh + 2 * gap, by = Math.min(height - stack - 18 * gui, Math.max(130 * gui, height / 2 - stack / 2));
		return new Rectangle[] { new Rectangle(bx, by, bw, bh), new Rectangle(bx, by + bh + gap, bw, bh) };
	}

	private void drawDeath(Graphics2D g0) {
		Graphics2D g = (Graphics2D) g0.create();
		g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
		g.setColor(new Color(150, 0, 0, 130)); g.fillRect(0, 0, width, height);   // red overlay
		g.setFont(pal(Font.BOLD, Math.max(42, Math.min(63, width / 24)))); g.setColor(Color.WHITE);
		String title = deathConfirm ? "Return to Main Menu?" : "You Died!";
		FontMetrics fm = g.getFontMetrics();
		g.drawString(title, (width - fm.stringWidth(title)) / 2, Math.max(70, height / 5) + 3); // same absolute Y as the settings title
		Rectangle[] r = deathRects();
		drawFrontButton(g, r[0], deathConfirm ? "Yes" : "Respawn", true);
		drawFrontButton(g, r[1], deathConfirm ? "Cancel" : "Return to Main Menu", true);
		g.dispose();
	}

	private void deathClick(int mx, int my) {
		Rectangle[] r = deathRects();
		if (deathConfirm) {
			if (r[0].contains(mx, my)) tasks.add(this::returnToMainMenu);
			else if (r[1].contains(mx, my)) deathConfirm = false;
		} else {
			if (r[0].contains(mx, my)) tasks.add(Nexus::respawn);
			else if (r[1].contains(mx, my)) deathConfirm = true;
		}
		repaint();
	}

	@Override
	public void paint(Graphics g) {
		synchronized (paintLock) { paintFrame(g); }
	}

	private void paintFrame(Graphics g) {
		Graphics2D g2d = (Graphics2D) g;
		BufferedImage img = screen;
		g2d.drawImage(img, 0, 0, width, height, null);
		if (!mainMenu && !hideEverything && display && (!paused || dialogOpen)) {
			g2d.drawImage(crosshair, width / 2 - CROSS / 2, height / 2 - CROSS / 2, null);
			gui(g2d);
		}
		if (mainMenu) {
			// Front-end uses screen-anchored coordinates; scale its controls/fonts, not
			// the entire canvas, so top/bottom UI never drifts off-screen.
			Graphics2D front = (Graphics2D) g2d.create();
			drawFrontMenu(front);
			front.dispose();
		}
		if (paused) {
			Graphics2D menuGraphics = (Graphics2D) g2d.create();
			menuGraphics.translate(width / 2.0, height / 2.0);
			double menuScale = menuUiScale();
			menuGraphics.scale(menuScale, menuScale);
			menuGraphics.translate(-width / 2.0, -height / 2.0);
			drawMenu(menuGraphics);
			menuGraphics.dispose();
		}
		if (dead) drawDeath(g2d);
		if (modifyUi) {
            Graphics2D modifyGraphics=(Graphics2D)g.create();
            double uiScale=Math.max(1,scale);
            modifyGraphics.translate(width/2.0,height/2.0);
            modifyGraphics.scale(uiScale,uiScale);
            modifyGraphics.translate(-width/2.0,-height/2.0);
            drawModifyUi(modifyGraphics);
        }
	}

	private static Path sharedWorldsPath() { return Paths.get(SHARED_WORLDS_DIR).toAbsolutePath(); }

	private static volatile List<File> worldListCache = Collections.emptyList();
	private static volatile long worldListStamp;

	static void invalidateWorldList() { worldListStamp = 0; }

	private static List<File> discoverSharedWorlds() {
		long now = System.currentTimeMillis();
		if (now - worldListStamp < 1500) return worldListCache;
		worldListStamp = now;
		return worldListCache = scanSharedWorlds();
	}

	private static List<File> scanSharedWorlds() {
		List<File> found = new ArrayList<>();
		try {
			Path dir = sharedWorldsPath();
			Files.createDirectories(dir);
			try (DirectoryStream<Path> ds = Files.newDirectoryStream(dir, "*.nexus")) {
				for (Path p : ds) if (validNexusFile(p.toFile())) found.add(p.toFile());
			}
		} catch (IOException ex) { frontMessage = "World folder unavailable: " + ex.getMessage(); }
		found.sort(Comparator.comparing(f -> f.getName().toLowerCase(Locale.ROOT)));
		return found;
	}

	private static final Map<String, long[]> worldModeCache = new ConcurrentHashMap<>(); // path -> {lastModified, survival}

	/** Reads the survival flag from the save header; cached until the file changes. */
	static boolean worldIsSurvival(File f) {
		long lm = f.lastModified();
		long[] c = worldModeCache.get(f.getPath());
		if (c != null && c[0] == lm) return c[1] != 0;
		boolean s = false;
		try (DataInputStream in = new DataInputStream(Files.newInputStream(f.toPath()))) {
			byte[] hdr = new byte[116];
			in.readFully(hdr);
			s = hdr[115] != 0;
		} catch (IOException ignored) {}
		worldModeCache.put(f.getPath(), new long[] { lm, s ? 1 : 0 });
		return s;
	}

	private static boolean validNexusFile(File file) {
		if (file == null || !file.isFile() || !file.getName().toLowerCase(Locale.ROOT).endsWith(".nexus")) return false;
		try (DataInputStream in = new DataInputStream(new BufferedInputStream(Files.newInputStream(file.toPath())))) { return in.readInt() == MAGIC; }
		catch (IOException ex) { return false; }
	}

	private static int frontGuiScale() {
		// Honor the same GUI scale as the in-game HUD, but step down when needed
		// so bottom-anchored controls (especially Back) remain inside the window.
		int requested = Math.max(1, Math.min(3, scale));
		int fit = Math.max(1, Math.min(width / 640, height / 480));
		return Math.max(1, Math.min(requested, fit));
	}

	private static final SimpleDateFormat WORLD_DATE_FMT = new SimpleDateFormat("MMM'.' d, yyyy 'at' H:mm:ss", Locale.ENGLISH);

	/** Trims text with a trailing ellipsis until it fits in maxW pixels. */
	private static String ellipsize(FontMetrics fm, String s, int maxW) {
		if (fm.stringWidth(s) <= maxW) return s;
		while (!s.isEmpty() && fm.stringWidth(s + "…") > maxW) s = s.substring(0, s.length() - 1);
		return s + "…";
	}

	static int createNameScroll; // horizontal scroll (px) of the Create World name field

	private void drawFrontMenu(Graphics2D g) {
		g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
		// Use the same neutral gray background for every main-menu screen.
		g.setColor(new Color(63, 63, 63, 127)); g.fillRect(0, 0, width, height);
		int gui = frontGuiScale();
		int panelW = Math.min(560 * gui, width - 32);
		int bw = Math.min(310 * gui, panelW - 36), bh = 42 * gui, gap = 10 * gui;
		int bx = (width - bw) / 2;
		g.setFont(pal(Font.BOLD, Math.max(30, Math.min(52, width / 22)) * gui)); g.setColor(Color.WHITE);
		FontMetrics fm = g.getFontMetrics();
		// The settings renderer supplies its own heading; don't draw the main-menu title here.
		if (frontScreen != 2 && frontScreen != 3) {
			String title = "Bitwise Nexus";
			g.drawString(title, (width - fm.stringWidth(title)) / 2, Math.max(76 * gui, height / 5));
			g.setFont(pal(Font.BOLD, 18 * gui)); g.setColor(new Color(225, 225, 225));
			String subtitle = "version " + VERSION; fm = g.getFontMetrics();
			g.drawString(subtitle, (width - fm.stringWidth(subtitle)) / 2, Math.max(108 * gui, height / 5 + 30 * gui));
		}
		int mainStack=3*bh+2*gap; int by = Math.min(height-mainStack-18*gui, Math.max(130*gui, height/2-mainStack/2));
		if (frontScreen == 0) {
			drawFrontButton(g,new Rectangle(bx,by,bw,bh),"Worlds",true);
			drawFrontButton(g,new Rectangle(bx,by+bh+gap,bw,bh),"Settings",true);
			drawFrontButton(g,new Rectangle(bx,by+2*(bh+gap),bw,bh),"Quit Game",true);
		} else if (frontScreen == 1) {
			List<File> worlds = discoverSharedWorlds();
			int listW=Math.min(620*gui,width-48), listTop=Math.max(78*gui, height/2-154*gui), listH=Math.min(238*gui,Math.max(82*gui,height/4+10*gui));
			int listX=(width-listW)/2;
			g.setColor(new Color(92,92,92,215)); g.fillRoundRect(listX,listTop,listW,listH,12*gui,12*gui);
			int rowH=36*gui, visible=Math.max(1,(listH-12*gui)/rowH);
			worldScroll = Math.max(0, Math.min(worldScroll, Math.max(0, worlds.size()-visible)));
			if (worldSelection < worldScroll) worldScroll = worldSelection;
			if (worldSelection >= worldScroll + visible) worldScroll = worldSelection - visible + 1;
			worldScroll = Math.max(0, Math.min(worldScroll, Math.max(0, worlds.size()-visible)));
			Graphics2D listGraphics=(Graphics2D)g.create();
			listGraphics.clipRect(listX+1,listTop+1,listW-2,listH-2);
			if(worlds.isEmpty()) { g.setFont(pal(Font.PLAIN,16*gui)); g.setColor(new Color(230,230,230)); String empty="No worlds"; fm=g.getFontMetrics(); g.drawString(empty,(width-fm.stringWidth(empty))/2,listTop+listH/2+fm.getAscent()/2); }
			for(int i=worldScroll;i<Math.min(worldScroll+visible,worlds.size());i++) {
				File f=worlds.get(i); Rectangle r=new Rectangle(listX+6*gui,listTop+6*gui+(i-worldScroll)*rowH,listW-12*gui,rowH-2*gui);
				listGraphics.setColor(i==worldSelection?new Color(125,125,125,235):new Color(65,65,65,220)); listGraphics.fillRoundRect(r.x,r.y,r.width,r.height,7*gui,7*gui);
				listGraphics.setColor(Color.WHITE); listGraphics.setFont(pal(Font.PLAIN,15*gui));
				String worldName=f.getName().endsWith(".nexus")?f.getName().substring(0,f.getName().length()-6):f.getName();
				String dateText=(worldIsSurvival(f)?"Survival":"Creative")+", modified: "+WORLD_DATE_FMT.format(new Date(f.lastModified()));
				FontMetrics rowFm=listGraphics.getFontMetrics();
				int pad=12*gui, maxTextW=Math.max(0,r.width-2*pad);
				int textY=r.y+(r.height+rowFm.getAscent())/2-3*gui;
				int dateW=rowFm.stringWidth(dateText);
				int nameRoom=maxTextW-dateW-12*gui;
				boolean showDate=nameRoom>=60*gui; // on very narrow windows, drop the date and keep the name readable
				if(!showDate) nameRoom=maxTextW;
				listGraphics.setColor(Color.WHITE);
				listGraphics.drawString(ellipsize(rowFm,worldName,nameRoom),r.x+pad,textY);
				if(showDate) {
					listGraphics.setColor(new Color(175,175,175));
					listGraphics.drawString(dateText,r.x+r.width-pad-dateW,textY);
				}
			}
			listGraphics.dispose();
			int actionW=Math.min(560*gui,width-48), actionX=(width-actionW)/2;
			int createY=Math.min(height-126*gui,listTop+listH+8*gui);
			drawFrontButton(g,new Rectangle(actionX,createY,actionW,bh),"Create World",true);
			int secondY = createY + bh + 8 * gui;
			int third = (actionW - 16 * gui) / 3;
			boolean hasSelection = !worlds.isEmpty() && worldSelection >= 0 && worldSelection < worlds.size();
			drawFrontButton(g, new Rectangle(actionX, secondY, third, bh), "Play Selected", hasSelection);
			drawFrontButton(g, new Rectangle(actionX + third + 8 * gui, secondY, third, bh), "Load File", true);
			drawFrontButton(g, new Rectangle(actionX + 2 * (third + 8 * gui), secondY, actionW - 2 * (third + 8 * gui), bh), "Delete", hasSelection);
			drawFrontButton(g, new Rectangle((width - Math.min(220 * gui, width - 40)) / 2, height - 52 * gui, Math.min(220 * gui, width - 40), 36 * gui), "Back", true);
		} else if (frontScreen == 2) {
			drawCreateWorld(g);
		} else if (frontScreen == 3) {
			// Use the in-game settings renderer and its bounded GUI-scale transform.
			boolean wasSettings=settingsMenu; int oldPage=settingsPage; settingsMenu=true;
			Graphics2D settingsGraphics=(Graphics2D)g.create();
			double s=menuUiScale();
			settingsGraphics.translate(width/2.0,height/2.0);
			settingsGraphics.scale(s,s);
			settingsGraphics.translate(-width/2.0,-height/2.0);
			drawMenu(settingsGraphics); settingsGraphics.dispose();
			settingsMenu=wasSettings; settingsPage=oldPage;
		}
		if (deleteConfirmWorld != null) {
		    g.setColor(new Color(0, 0, 0, 175));
		    g.fillRect(0, 0, width, height);

		    int dialogW = Math.min(440 * gui, width - 32);
		    int dialogH = 142 * gui;
		    int dx = (width - dialogW) / 2;
		    int dy = (height - dialogH) / 2;

		    g.setColor(new Color(48, 48, 48, 250));
		    g.fillRoundRect(dx, dy, dialogW, dialogH, 14 * gui, 14 * gui);
		    g.setColor(new Color(190, 190, 190));
		    g.drawRoundRect(dx, dy, dialogW, dialogH, 14 * gui, 14 * gui);

		    g.setFont(pal(Font.BOLD, 18 * gui));
		    g.setColor(Color.WHITE);
		    FontMetrics dfm = g.getFontMetrics();
		    String question = "Delete this world?";
		    g.drawString(question,
		            dx + (dialogW - dfm.stringWidth(question)) / 2,
		            dy + 34 * gui);

		    g.setFont(pal(Font.PLAIN, 13 * gui));
		    dfm = g.getFontMetrics();

		    String worldName = deleteConfirmWorld.getName();
		    if (worldName.endsWith(".nexus")) {
		        worldName = worldName.substring(0, worldName.length() - 6);
		    }

		    String message = "Are you sure you want to delete " + worldName + "?";
		    g.setColor(new Color(220, 220, 220));
		    g.drawString(ellipsize(dfm, message, dialogW - 28 * gui),
		            dx + 14 * gui, dy + 61 * gui);

		    int dbw = (dialogW - 30 * gui) / 2;
		    int dby = dy + 82 * gui;

		    drawFrontButton(g,
		            new Rectangle(dx + 10 * gui, dby, dbw, 38 * gui),
		            "Cancel", true);

		    drawFrontButton(g,
		            new Rectangle(dx + 20 * gui + dbw, dby,
		                    dialogW - 30 * gui - dbw, 38 * gui),
		            "Delete World", true);
		}
		if (!frontMessage.isEmpty()) { g.setFont(pal(Font.PLAIN,13*gui)); g.setColor(new Color(255,190,130)); fm=g.getFontMetrics(); g.drawString(frontMessage,(width-fm.stringWidth(frontMessage))/2,height-18*gui); }
	}

	private static void drawFrontButton(Graphics2D g, Rectangle r, String text, boolean enabled) {
		g.setColor(enabled?new Color(72,72,72,235):new Color(42,42,42)); g.fillRoundRect(r.x,r.y,r.width,r.height,10,10);
		g.setColor(enabled?new Color(165,165,165):new Color(75,75,75)); g.drawRoundRect(r.x,r.y,r.width,r.height,10,10);
		g.setFont(pal(Font.BOLD,16*frontGuiScale())); g.setColor(enabled?Color.WHITE:new Color(135,135,135)); FontMetrics fm=g.getFontMetrics();
		g.drawString(text,r.x+(r.width-fm.stringWidth(text))/2,r.y+(r.height+fm.getAscent()-fm.getDescent())/2+2*frontGuiScale());
	}

	private File deleteConfirmWorld = null;

    private static boolean deleteWorldFiles(File world) {
        if (world == null || !world.exists()) return false;

        try {
            if (world.isDirectory()) {
                File[] children = world.listFiles();
                if (children == null) return false;

                for (File child : children) {
                    if (!deleteWorldFiles(child)) return false;
                }
            }

            return world.delete();
        } catch (SecurityException e) {
            return false;
        }
    }

    private void frontMenuClick(int mx, int my) {
		int gui = frontGuiScale();

		if (deleteConfirmWorld != null) {
		    int dialogW = Math.min(440 * gui, width - 32);
		    int dialogH = 142 * gui;
		    int dx = (width - dialogW) / 2;
		    int dy = (height - dialogH) / 2;
		    int dbw = (dialogW - 30 * gui) / 2;
		    int dby = dy + 82 * gui;

		    Rectangle cancelRect = new Rectangle(
		        dx + 10 * gui, dby, dbw, 38 * gui
		    );

		    Rectangle deleteRect = new Rectangle(
		        dx + 20 * gui + dbw, dby,
		        dialogW - 30 * gui - dbw, 38 * gui
		    );

		    if (cancelRect.contains(mx, my)) {
		        deleteConfirmWorld = null;
		    } else if (deleteRect.contains(mx, my)) {
		        File target = deleteConfirmWorld;
		        deleteConfirmWorld = null;

		        if (target.exists() && deleteWorldFiles(target)) {
		            invalidateWorldList();
		            List<File> remaining = discoverSharedWorlds();
		            worldSelection = remaining.isEmpty()
		                ? -1
		                : Math.min(worldSelection, remaining.size() - 1);
		            worldScroll = Math.min(
		                worldScroll,
		                Math.max(0, remaining.size() - 1)
		            );
		            frontMessage = "World deleted.";
		        } else {
		            frontMessage = "Could not delete world.";
		        }
		    } else if (mx < dx || mx >= dx + dialogW
		            || my < dy || my >= dy + dialogH) {
		        deleteConfirmWorld = null;
		    }

		    repaint();
		    return;
		}

		// Handle the delete confirmation dialog first.
		if (deleteConfirmWorld != null) {
			int dialogW = Math.min(440 * gui, width - 32);
			int dialogH = 142 * gui;
			int dx = (width - dialogW) / 2;
			int dy = (height - dialogH) / 2;
			int dbw = (dialogW - 30 * gui) / 2;
			int dby = dy + 82 * gui;

			if (new Rectangle(dx + 10 * gui, dby, dbw, 38 * gui).contains(mx, my)) {
				// Cancel deletion.
				deleteConfirmWorld = null;
				frontMessage = "";
			} else if (new Rectangle(dx + 20 * gui + dbw, dby, dialogW - 30 * gui - dbw, 38 * gui).contains(mx, my)) {
				// Confirm deletion.
				File target = deleteConfirmWorld;
				deleteConfirmWorld = null;

				if (deleteWorldFiles(target)) {
					invalidateWorldList();
					List<File> remaining = discoverSharedWorlds();
					worldSelection = Math.max(0, Math.min(worldSelection, remaining.size() - 1));
					worldScroll = Math.max(0, Math.min(worldScroll, Math.max(0, remaining.size() - 1)));
					frontMessage = "World deleted.";
				} else {
					frontMessage = "Could not delete world.";
				}
			} else if (!new Rectangle(dx, dy, dialogW, dialogH).contains(mx, my)) {
				// Clicking outside dismisses the dialog without deleting.
				deleteConfirmWorld = null;
			}

			repaint();
			return;
		}

		int bw = Math.min(310 * gui, Math.min(560 * gui, width - 32) - 36);
		int bh = 42 * gui;
		int gap = 10 * gui;
		int bx = (width - bw) / 2;
		int mainStack = 3 * bh + 2 * gap;
		int by = Math.min(height - mainStack - 18 * gui, Math.max(130 * gui, height / 2 - mainStack / 2));

		if (frontScreen == 0) {
			if (new Rectangle(bx, by, bw, bh).contains(mx, my)) {
				frontScreen = 1;
				worldSelection = 0;
				worldScroll = 0;
				frontMessage = "";
			} else if (new Rectangle(bx, by + bh + gap, bw, bh).contains(mx, my)) {
				frontScreen = 3;
				settingsPage = 0;
			} else if (new Rectangle(bx, by + 2 * (bh + gap), bw, bh).contains(mx, my)) {
				saveOnShutdown();
				frame.dispose();
				System.exit(0);
			}

		} else if (frontScreen == 1) {
			invalidateWorldList();
			List<File> worlds = discoverSharedWorlds();

			int listW = Math.min(620 * gui, width - 48);
			int listTop = Math.max(78 * gui, height / 2 - 154 * gui);
			int listH = Math.min(238 * gui, Math.max(82 * gui, height / 4 + 10 * gui));
			int listX = (width - listW) / 2;
			int rowH = 36 * gui;
			int visible = Math.max(1, (listH - 12 * gui) / rowH);

			if (mx >= listX && mx <= listX + listW && my >= listTop + 6 * gui
					&& my < listTop + 6 * gui + visible * rowH) {
				int i = worldScroll + (my - (listTop + 6 * gui)) / rowH;

				if (i >= 0 && i < worlds.size()) {
					worldSelection = i;

					if (lastFrontClickIndex == i && System.currentTimeMillis() - lastFrontClickTime < 450) {
						File f = worlds.get(i);
						tasks.add(() -> doLoad(f));
						frontMessage = "Loading " + f.getName() + "…";
					}

					lastFrontClickIndex = i;
					lastFrontClickTime = System.currentTimeMillis();
				}
			}

			int actionW = Math.min(560 * gui, width - 48);
			int actionX = (width - actionW) / 2;
			int createY = Math.min(height - 126 * gui, listTop + listH + 8 * gui);
			int secondY = createY + bh + 8 * gui;
			int third = (actionW - 16 * gui) / 3;

			boolean hasSelection = !worlds.isEmpty() && worldSelection >= 0 && worldSelection < worlds.size();

			if (new Rectangle(actionX, createY, actionW, bh).contains(mx, my)) {
				frontScreen = 2;
				createWorldName = "";
				createNameCaret = createNameAnchor = 0;
				createNameScroll = 0;
				ampEdit = Double.toString(amp);
				ampCaret = ampAnchor = ampEdit.length();
				ampEditFocused = false;
				createSurvival = false;
				frontMessage = "";

			} else if (hasSelection && new Rectangle(actionX, secondY, third, bh).contains(mx, my)) {
				File f = worlds.get(worldSelection);
				tasks.add(() -> doLoad(f));
				frontMessage = "Loading " + f.getName() + "…";

			} else if (new Rectangle(actionX + third + 8 * gui, secondY, third, bh).contains(mx, my)) {
				loadExternalWorld();

			} else if (hasSelection
					&& new Rectangle(actionX + 2 * (third + 8 * gui), secondY, actionW - 2 * (third + 8 * gui), bh)
							.contains(mx, my)) {
				deleteConfirmWorld = worlds.get(worldSelection);
				frontMessage = "";

			} else if (new Rectangle((width - Math.min(220 * gui, width - 40)) / 2, height - 52 * gui,
					Math.min(220 * gui, width - 40), 36 * gui).contains(mx, my)) {
				frontScreen = 0;
				frontMessage = "";
			}

		} else if (frontScreen == 2) {
			createWorldClick(mx, my);

		} else if (frontScreen == 3) {
			settingsMenu = true;
			menuClick(mx, my);

			if (!settingsMenu) {
				frontScreen = 0;
				settingsPage = 0;
			}
		}

		repaint();
	}

	private void returnToMainMenu() {
		try {
			if (persistentStorage && activeSaveFile != null) {
				long deadline = System.currentTimeMillis() + 15000L;
				while (saveInProgress.get() && System.currentTimeMillis() < deadline) Thread.sleep(25L);
				flushDirty();
				writeSave(new SaveSnapshot(activeSaveFile, changedChunkSnapshot()));
				lastPersistentSave = System.currentTimeMillis();
			}
		} catch (Throwable t) { System.err.println("Autosave before returning to menu failed: " + t); }
		// Detach the saved world from the menu preview so no later autosave/shutdown
		// snapshot can accidentally serialize the preview's forced camera position.
		saveRequested = false;
		requestedSaveFile = null;
		activeSaveFile = null;
		persistentStorage = false;
		survival = false; dead = false; deathConfirm = false; leftDown = false; health = MAX_HEALTH; resetBreak();
		paused = false; settingsMenu = false; quitConfirm = false; dialogOpen = false;
		mainMenu = true; frontScreen = 0; frontMessage = "";
		x.setValue(15493); y.setValue(96); z.setValue(17236);
		prevX.set(x); prevY.set(y); prevZ.set(z);
		yaw = 1.2; pitch = -2.0 / 3.0; setDist(368);
		velX = velY = velZ = 0; needGround = false;
		fly = true; mouseLookArmed = false;
		lock = false; focus = true;
		if (frame != null) frame.setCursor(Cursor.getDefaultCursor());
		center(); reloadChunks(false); lastMenuFrameNs = 0;
		repaint();
	}

	private void loadExternalWorld() {
		JFileChooser fc=new JFileChooser(); fc.setDialogTitle("Load Nexus world"); fc.setAcceptAllFileFilterUsed(false); fc.setFileFilter(new FileNameExtensionFilter("Nexus world (*.nexus)","nexus")); chooser(fc);
		if(fc.showOpenDialog(frame)!=JFileChooser.APPROVE_OPTION)return;
		File f=fc.getSelectedFile(); if(!validNexusFile(f)){frontMessage="Not a valid Nexus world.";return;}
		tasks.add(()->doLoad(f)); frontMessage="Loading "+f.getName()+"…";
	}

	private static double createUiScale() {
	    double requested = Math.max(1, Math.min(3, scale));
	    return Math.min(requested, Math.max(0.5, (height - 24.0) / CREATE_H));
	}

	/** {x0, w, top} in menu space. */
	private static int[] createGeom() {
	    double s = createUiScale();
	    int w = Math.max(240, Math.min(420, (int) (width / s) - 24));
	    return new int[] { (width - w) / 2, w, height / 2 - CREATE_H / 2 };
	}

	private void drawCreateWorld(Graphics2D g0) {
	    Graphics2D g = (Graphics2D) g0.create();
	    g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
	    double s = createUiScale();
	    g.translate(width / 2.0, height / 2.0); g.scale(s, s); g.translate(-width / 2.0, -height / 2.0);
	    int[] gm = createGeom(); int x0 = gm[0], w = gm[1], T = gm[2];
	    String name = createWorldName;
	    g.setColor(Color.WHITE); g.setFont(pal(Font.BOLD, 22)); centered(g, "Create World", width / 2, T + 18);

	    int fy = T + 30, fh = 36;
	    g.setColor(new Color(78, 78, 78, 230)); g.fillRoundRect(x0, fy, w, fh, 8, 8);
	    g.setFont(pal(Font.PLAIN, 16)); FontMetrics fm = g.getFontMetrics();
	    int ty = fy + (fh + fm.getAscent() - fm.getDescent()) / 2, innerW = w - 20, textLeft = x0 + 10;
	    int caretIdx = Math.max(0, Math.min(name.length(), createNameCaret));
	    int caretPx = fm.stringWidth(name.substring(0, caretIdx));
	    createNameScroll = Math.max(0, Math.min(createNameScroll, caretPx));
	    if (caretPx - createNameScroll > innerW) createNameScroll = caretPx - innerW;
	    createNameScroll = Math.min(createNameScroll, Math.max(0, fm.stringWidth(name) - innerW));
	    int tx = textLeft - createNameScroll;
	    Graphics2D fg = (Graphics2D) g.create();
	    fg.clipRect(textLeft, fy, innerW + 1, fh);
	    int a = Math.max(0, Math.min(name.length(), Math.min(createNameCaret, createNameAnchor)));
	    int b = Math.max(0, Math.min(name.length(), Math.max(createNameCaret, createNameAnchor)));
	    if (b > a) {
	        int sx = tx + fm.stringWidth(name.substring(0, a)), ex = tx + fm.stringWidth(name.substring(0, b));
	        fg.setColor(new Color(125, 125, 125, 220)); fg.fillRect(sx, fy + 4, ex - sx, fh - 8);
	    }
	    fg.setColor(Color.WHITE); fg.drawString(name, tx, ty);
	    if (System.currentTimeMillis() % 1000 < 550) fg.drawLine(tx + caretPx, fy + 6, tx + caretPx, fy + fh - 6);
	    fg.dispose();

	    g.setColor(new Color(225, 225, 225)); g.setFont(pal(Font.PLAIN, 12));
	    g.drawString("Name: letters, numbers, _ and - (max 32)", x0, T + 82);
	    drawButton(g, new Rectangle(x0, T + 90, w, 32), "Gamemode: " + (createSurvival ? "Survival" : "Creative"));

	    g.setFont(pal(Font.BOLD, 15));
	    drawWorldSettings(g, x0, w, T + 120);
	    int by = T + 320, half = (w - 8) / 2;
	    drawButton(g, new Rectangle(x0, by, half, 36), "Cancel");
	    drawButton(g, new Rectangle(x0 + half + 8, by, half, 36), "Create");
	    g.dispose();
	}

	private static void drawExtraSettings(Graphics2D g, int x0, int w, int e) {
	    int halfW = (w - 10) / 2;
	    drawButton(g,new Rectangle(x0,e,halfW,28),"Classic Mode: "+(classic?"ON":"OFF"));
	    drawButton(g,new Rectangle(x0+halfW+10,e,halfW,28),"Bitwise Mode: "+(xor?"ON":"OFF"));
	    drawButton(g,new Rectangle(x0,e+32,halfW,28),"Freeze Time: "+(freezeTime?"ON":"OFF"));
	    drawButton(g,new Rectangle(x0+halfW+10,e+32,halfW,28),"Lantern: "+(lanternEnabled?"ON":"OFF"));
	    drawSlider(g,x0,e+80,w,"AO Strength",AO_STRENGTH,String.format(Locale.ROOT,"%.2f%s",AO_STRENGTH,AO_STRENGTH==0?" (Off)":""));
	    drawSlider(g,x0,e+130,w,"Explosion Power",(power-1)/126.0,Integer.toString(power),survival);
	    g.setColor(Color.WHITE); g.drawString("Fog Color (RGB 0-1)",x0,e+186);
	    double[] rgb = {Math.max(0,Math.min(1,red)),Math.max(0,Math.min(1,green)),Math.max(0,Math.min(1,blue))};
	    String[] labels = {"R","G","B"};
	    for (int i=0;i<3;i++) {
	        int bx=x0+i*(w/3), bw=w/3-8;
	        g.setColor(new Color(55,55,60)); g.fillRoundRect(bx,e+194,bw,28,6,6);
	        g.setColor(Color.WHITE); g.drawString(labels[i]+": "+String.format(Locale.ROOT,"%.3f",rgb[i])+(rgbEditChannel==i?"  > "+rgbEdit:""),bx+8,e+213);
	    }
	    int fogColor=(int)(rgb[0]*255)<<16|(int)(rgb[1]*255)<<8|(int)(rgb[2]*255);
	    g.setColor(new Color(fogColor)); g.fillRoundRect(x0,e+228,64,26,6,6);
	    drawButton(g,new Rectangle(x0+72,e+226,110,30),"Hex: #"+(rgbEditChannel==-2?rgbEdit:String.format(Locale.ROOT,"%06X",fogColor)));
	    drawButton(g,new Rectangle(x0+190,e+226,w-190,30),"Modify Fog Color");
	}

	private boolean extraSettingsClick(int mx, int my, int x0, int w, int e) {
	    int halfW = (w - 10) / 2;
	    if (my>=e && my<=e+28) { if (mx<x0+halfW+5) classic=!classic; else toggleXor(); }
	    else if (my>=e+32 && my<=e+60) { if (mx<x0+halfW+5) freezeTime=!freezeTime; else lanternEnabled=!lanternEnabled; }
	    else if (my>=e+98 && my<=e+122) AO_STRENGTH=Math.round(Math.max(0,Math.min(1,(mx-x0)/(double)w))*100)/100.0;
	    else if (my>=e+148 && my<=e+172) { if (!survival) power=(byte)(1+Math.round(Math.max(0,Math.min(1,(mx-x0)/(double)w))*126)); }
	    else if (my>=e+194 && my<=e+222) { rgbEditChannel=Math.max(0,Math.min(2,(mx-x0)/(w/3))); rgbEdit=""; }
	    else if (my>=e+226 && my<=e+256) {
	        if (mx>=x0+72 && mx<x0+182) { rgbEditChannel=-2; rgbEdit=""; }
	        else if (mx>=x0+190) {
	            Color c=pickFogColor(new Color((float)red,(float)green,(float)blue));
	            if (c!=null) { red=c.getRed()/255.0; green=c.getGreen()/255.0; blue=c.getBlue()/255.0; }
	        }
	    } else return false;
	    return true;
	}

	static final int CREATE_H = 370;
	static final double[] AMPS = { 1, 10, 100 };
	static final String[] AMP_NAMES = { "Normal Amp.", "High Amp.", "Ultra Amp." };

	private static void drawWorldSettings(Graphics2D g, int x0, int w, int y0) {
	    drawButton(g,new Rectangle(x0,y0+18,w,32),"Cave Generation: "+(caves?"ON":"OFF"));
	    drawButton(g,new Rectangle(x0,y0+56,w,32),"3D Terrain: "+(terrain3D?"ON":"OFF"));
	    int bw = w / 3;
	    for (int i = 0; i < 3; i++)
	        drawButton(g,new Rectangle(x0+i*bw,y0+118,bw-8,30),AMP_NAMES[i],amp==AMPS[i]?3f:1f); // thick border = selected
	    int fy = y0 + 154;
	    g.setColor(new Color(45,47,54)); g.fillRoundRect(x0,fy,w,26,6,6);
	    g.setColor(ampEditFocused ? new Color(120,190,255) : new Color(90,93,104));
	    g.drawRoundRect(x0,fy,w,26,6,6);
	    String av = ampEdit == null ? "" : ampEdit;
	    FontMetrics fm = g.getFontMetrics();
	    g.setColor(new Color(220,224,232)); g.drawString("Amp:",x0+8,fy+17);
	    int tx = x0 + 52;
	    if (ampEditFocused) {
            int aa=Math.max(0,Math.min(av.length(),Math.min(ampCaret,ampAnchor)));
            int ab=Math.max(0,Math.min(av.length(),Math.max(ampCaret,ampAnchor)));
            if(aa<ab){int sx=tx+fm.stringWidth(av.substring(0,aa)), ex=tx+fm.stringWidth(av.substring(0,ab));g.setColor(new Color(75,112,165));g.fillRect(sx,fy+4,Math.max(1,ex-sx),18);}
        }
	    g.setColor(Color.WHITE); g.drawString(av,tx,fy+17);
	    if (ampEditFocused && System.currentTimeMillis()%1000<550) {
	        int ci=Math.max(0,Math.min(av.length(),ampCaret));
	        int cx=tx+fm.stringWidth(av.substring(0,ci));
	        g.drawLine(cx,fy+4,cx,fy+22);
	    }
	}

	private boolean worldSettingsClick(int mx, int my, int x0, int w, int y0) {
	    if (my>=y0+18 && my<=y0+50) caves = !caves;
	    else if (my>=y0+56 && my<=y0+88) terrain3D = !terrain3D;
	    else if (my>=y0+118 && my<=y0+148) { amp = AMPS[Math.max(0,Math.min(2,(mx-x0)/(w/3)))]; ampEdit=Double.toString(amp); ampCaret=ampAnchor=ampEdit.length(); ampEditFocused=false; }
	    else if (my>=y0+154 && my<=y0+180) {
	        ampEditFocused=true;
	        FontMetrics fm=frame.getFontMetrics(pal(Font.PLAIN,15));
	        int target=Math.max(0,mx-(x0+52)); ampCaret=0;
	        while(ampCaret<ampEdit.length() && fm.stringWidth(ampEdit.substring(0,ampCaret+1))<target) ampCaret++;
	        ampAnchor=ampCaret;
	    }
	    else return false;
	    return true;
	}

	private void createWorldClick(int sx, int sy) {
	    double s = createUiScale();
	    int mx = (int) Math.round(width / 2.0 + (sx - width / 2.0) / s);
	    int my = (int) Math.round(height / 2.0 + (sy - height / 2.0) / s);
	    int[] gm = createGeom(); int x0 = gm[0], w = gm[1], T = gm[2];
	    if (new Rectangle(x0, T + 30, w, 36).contains(mx, my)) {
            ampEditFocused=false;
	        rgbEditChannel = -1; rgbEdit = "";
	        FontMetrics fm = frame.getFontMetrics(pal(Font.PLAIN, 16));
	        String name = createWorldName; int target = mx - (x0 + 10) + createNameScroll, c = 0;
	        while (c < name.length() && fm.stringWidth(name.substring(0, c + 1)) < target) c++;
	        createNameCaret = createNameAnchor = c;
	        return;
	    }
	    if (new Rectangle(x0, T + 90, w, 32).contains(mx, my)) { ampEditFocused = false; createSurvival = !createSurvival; return; }
	    if (worldSettingsClick(mx, my, x0, w, T + 120)) return;
	    int by = T + 320, half = (w - 8) / 2;
	    if (new Rectangle(x0, T+120+154, w, 26).contains(mx,my)) {
	        ampEditFocused=true;
	        FontMetrics fm=frame.getFontMetrics(pal(Font.PLAIN,15));
	        int target=Math.max(0,mx-(x0+52)); ampCaret=0;
	        while(ampCaret<ampEdit.length() && fm.stringWidth(ampEdit.substring(0,ampCaret+1))<target) ampCaret++;
	        ampAnchor=ampCaret;
	    }
	    else if (new Rectangle(x0, by, half, 36).contains(mx, my)) { ampEditFocused=false; frontScreen = 1; frontMessage = ""; }
	    else if (new Rectangle(x0 + half + 8, by, half, 36).contains(mx, my)) { ampEditFocused=false; createWorld(); }
	    else ampEditFocused=false;
	}

	private void createWorld() {
		fly = false;
		worldLoading = true;
		worldLoadReadyAt = 0L;
		velX = velY = velZ = 0;
		mouseLookArmed = false;
		String name=createWorldName;
		if(name==null||!name.matches("[A-Za-z0-9_ -]{1,32}")||name.trim().isEmpty()){worldLoading=false;frontMessage="Use letters, numbers, spaces, _ or - (1–32 chars).";return;}
		try {
			Files.createDirectories(sharedWorldsPath()); File target=sharedWorldsPath().resolve(name+".nexus").toFile();
			if(target.exists()){worldLoading=false;frontMessage="A world with that name already exists.";return;}
			clearSaved(); savedChunks.clear(); chunkCache.clear(); pendingWrites.clear(); persistentStorage=false; activeSaveFile=null;
			survival = createSurvival;
			resetSurvivalState();
			spawn();
			yaw = 0; pitch = 0;
			center(); reloadChunks(false); needGround=false; time=0; velX=velY=velZ=0;
			worldSpawnX.set(x); worldSpawnY.set(y); worldSpawnZ.set(z);
			activeSaveFile=target; persistentStorage=true; lastPersistentSave=System.currentTimeMillis(); mainMenu=false; lock=true; focus=true; frame.setCursor(hidden); center();
			doSave(target); frontMessage=""; frontScreen=0;
			invalidateWorldList();
		} catch(Exception ex){worldLoading=false;worldLoadReadyAt=0L;frontMessage="Could not create world: "+ex.getMessage(); mainMenu=true;}
	}

	private void handleFrontKey(KeyEvent e) {
		int code=e.getKeyCode(); boolean ctrl=e.isControlDown()||e.isMetaDown();
		if ((frontScreen == 3 || frontScreen == 2) && handleRgbEditKey(code)) return;
		if(code==KeyEvent.VK_ESCAPE){if(frontScreen==0){return;} if(frontScreen==3){frontScreen=0;settingsMenu=false;settingsPage=0;} else if(frontScreen==2){frontScreen=1;frontMessage="";} else {frontScreen=0;frontMessage="";} return;}
		if(frontScreen==3){if(code==KeyEvent.VK_ENTER){settingsMenu=false;settingsPage=0;frontScreen=0;}return;}
		if(frontScreen == 1) {
			if (code == KeyEvent.VK_UP || code == KeyEvent.VK_DOWN) {
		        List<File> worlds = discoverSharedWorlds();
		        int count = worlds.size();

		        if (count > 0) {
		            worldSelection = (worldSelection + (code == KeyEvent.VK_DOWN ? 1 : -1) + count) % count;
		        } else {
		            worldSelection = 0;
		        }

		        repaint();
		        return;
		    }

		    if (code == KeyEvent.VK_ENTER) {
		        List<File> worlds = discoverSharedWorlds();
		        if (worldSelection >= 0 && worldSelection < worlds.size()) {
		            File selected = worlds.get(worldSelection);
		            tasks.add(() -> doLoad(selected));
		            frontMessage = "Loading " + selected.getName() + "…";
		        }
		        return;
		    }
		}
		if(frontScreen!=2)return;
		String value=createWorldName; int a=Math.min(createNameCaret,createNameAnchor), b=Math.max(createNameCaret,createNameAnchor);
		if(ctrl&&code==KeyEvent.VK_A){createNameAnchor=0;createNameCaret=value.length();return;}
		if(ctrl&&(code==KeyEvent.VK_C||code==KeyEvent.VK_X)){if(a!=b)try{Toolkit.getDefaultToolkit().getSystemClipboard().setContents(new StringSelection(value.substring(a,b)),null);}catch(Exception ignored){} if(code==KeyEvent.VK_X&&a!=b){createWorldName=value.substring(0,a)+value.substring(b);createNameCaret=createNameAnchor=a;}return;}
		if(ctrl&&code==KeyEvent.VK_V){try{Object data=Toolkit.getDefaultToolkit().getSystemClipboard().getData(DataFlavor.stringFlavor);if(data instanceof String){String clip=((String)data).replaceAll("[^A-Za-z0-9_ -]","");int room=32-(value.length()-(b-a));if(clip.length()>room)clip=clip.substring(0,Math.max(0,room));createWorldName=value.substring(0,a)+clip+value.substring(b);createNameCaret=createNameAnchor=a+clip.length();}}catch(Exception ignored){}return;}
        if (ampEditFocused) {
            String av=ampEdit==null?"":ampEdit;
            int aa=Math.min(ampCaret,ampAnchor), ab=Math.max(ampCaret,ampAnchor);
            if(ctrl&&code==KeyEvent.VK_A){ampAnchor=0;ampCaret=av.length();return;}
            if(ctrl&&(code==KeyEvent.VK_C||code==KeyEvent.VK_X)){
                if(aa!=ab)try{Toolkit.getDefaultToolkit().getSystemClipboard().setContents(new StringSelection(av.substring(aa,ab)),null);}catch(Exception ignored){}
                if(code==KeyEvent.VK_X&&aa!=ab){ampEdit=av.substring(0,aa)+av.substring(ab);ampCaret=ampAnchor=aa;} return;
            }
            if(ctrl&&code==KeyEvent.VK_V){
                try{Object d=Toolkit.getDefaultToolkit().getSystemClipboard().getData(DataFlavor.stringFlavor);if(d instanceof String){String clip=((String)d).replaceAll("[^0-9eE+\\-.]","");ampEdit=av.substring(0,aa)+clip+av.substring(ab);ampCaret=ampAnchor=aa+clip.length();}}catch(Exception ignored){} return;
            }
            if(code==KeyEvent.VK_ENTER){
                try{double v=Double.parseDouble(av.trim());if(!Double.isFinite(v)||v<=0)throw new NumberFormatException();amp=v;ampEdit=Double.toString(v);ampCaret=ampAnchor=ampEdit.length();ampEditFocused=false;}
                catch(NumberFormatException ex){frontMessage="Amplitude must be a finite positive number.";return;}
                if(!createWorldName.isEmpty())createWorld();return;
            }
            if(code==KeyEvent.VK_LEFT||code==KeyEvent.VK_RIGHT){
                int pos=ampCaret;
                if(ctrl){if(code==KeyEvent.VK_LEFT){while(pos>0&&Character.isWhitespace(av.charAt(pos-1)))pos--;while(pos>0&&!Character.isWhitespace(av.charAt(pos-1)))pos--;}else{while(pos<av.length()&&!Character.isWhitespace(av.charAt(pos)))pos++;while(pos<av.length()&&Character.isWhitespace(av.charAt(pos)))pos++;}}
                else if(e.isShiftDown())pos=Math.max(0,Math.min(av.length(),pos+(code==KeyEvent.VK_LEFT?-1:1)));
                else if(aa!=ab)pos=code==KeyEvent.VK_LEFT?aa:ab;else pos=Math.max(0,Math.min(av.length(),pos+(code==KeyEvent.VK_LEFT?-1:1)));
                ampCaret=pos;if(!e.isShiftDown())ampAnchor=pos;return;
            }
            if(code==KeyEvent.VK_HOME||code==KeyEvent.VK_END){ampCaret=code==KeyEvent.VK_HOME?0:av.length();if(!e.isShiftDown())ampAnchor=ampCaret;return;}
            if(code==KeyEvent.VK_BACK_SPACE||code==KeyEvent.VK_DELETE){
                if(aa!=ab){ampEdit=av.substring(0,aa)+av.substring(ab);ampCaret=ampAnchor=aa;}
                else if(code==KeyEvent.VK_BACK_SPACE&&ampCaret>0){ampEdit=av.substring(0,ampCaret-1)+av.substring(ampCaret);ampCaret--;ampAnchor=ampCaret;}
                else if(code==KeyEvent.VK_DELETE&&ampCaret<av.length()){ampEdit=av.substring(0,ampCaret)+av.substring(ampCaret+1);ampAnchor=ampCaret;}
                return;
            }
            char ac=e.getKeyChar();
            if(ac!=KeyEvent.CHAR_UNDEFINED&&("0123456789.eE+-".indexOf(ac)>=0)&&av.length()<32){ampEdit=av.substring(0,aa)+ac+av.substring(ab);ampCaret=ampAnchor=aa+1;}
            return;
        }
		if(code==KeyEvent.VK_ENTER){if(!createWorldName.isEmpty())createWorld();return;}
		if(code==KeyEvent.VK_LEFT){int pos=createNameCaret;if(ctrl){while(pos>0&&Character.isLetterOrDigit(value.charAt(pos-1)))pos--;while(pos>0&&value.charAt(pos-1)==' ')pos--;}else if(!e.isShiftDown()&&a!=b)pos=a;else pos=Math.max(0,pos-1);createNameCaret=pos;if(!e.isShiftDown())createNameAnchor=pos;return;}
		if(code==KeyEvent.VK_RIGHT){int pos=createNameCaret;if(ctrl){while(pos<value.length()&&Character.isLetterOrDigit(value.charAt(pos)))pos++;while(pos<value.length()&&value.charAt(pos)==' ')pos++;}else if(!e.isShiftDown()&&a!=b)pos=b;else pos=Math.min(value.length(),pos+1);createNameCaret=pos;if(!e.isShiftDown())createNameAnchor=pos;return;}
		if(code==KeyEvent.VK_HOME){createNameCaret=0;if(!e.isShiftDown())createNameAnchor=0;return;} if(code==KeyEvent.VK_END){createNameCaret=value.length();if(!e.isShiftDown())createNameAnchor=createNameCaret;return;}
		if(code==KeyEvent.VK_BACK_SPACE||code==KeyEvent.VK_DELETE){if(a!=b){createWorldName=value.substring(0,a)+value.substring(b);createNameCaret=createNameAnchor=a;}else if(code==KeyEvent.VK_BACK_SPACE&&createNameCaret>0){int from=ctrl?createNameCaret-1:createNameCaret-1;if(ctrl)while(from>0&&Character.isLetterOrDigit(value.charAt(from-1)))from--;createWorldName=value.substring(0,from)+value.substring(createNameCaret);createNameCaret=createNameAnchor=from;}else if(code==KeyEvent.VK_DELETE&&createNameCaret<value.length()){int to=createNameCaret+1;if(ctrl)while(to<value.length()&&Character.isLetterOrDigit(value.charAt(to)))to++;createWorldName=value.substring(0,createNameCaret)+value.substring(to);createNameAnchor=createNameCaret;}return;}
		char ch=e.getKeyChar(); if(ch!=KeyEvent.CHAR_UNDEFINED&&createWorldName.length()<32&&(Character.isLetterOrDigit(ch)||ch=='_'||ch=='-'||ch==' ')){createWorldName=value.substring(0,a)+ch+value.substring(b);createNameCaret=createNameAnchor=a+1;}
	}

	private static Rectangle menuRect(int row) {
		int w = Math.min(360, Math.max(260, width - 40));
		int h = 38, gap = 10;
		int count = settingsMenu ? 1 : 5;
		int total = count * h + (count - 1) * gap;
		int top = Math.max(100, (height - total) / 2 + 10);
		return new Rectangle((width - w) / 2, top + row * (h + gap), w, h);
	}

	private static double menuUiScale() {
		// Scale controls up with the selected/automatic GUI scale, but cap the
		// effective transform so the tallest page and its Back button stay visible.
		double requested = Math.max(1, Math.min(3, scale));
		double fit = Math.max(0.75, (height - 24.0) / settingsContentHeight());
		return Math.min(requested, fit);
	}

	private static int settingsContentHeight() { return settingsPage == 1 ? 650 : 310; }

	private static int settingsY0() {
	    int base = (height - settingsContentHeight()) / 2;
	    return settingsPage == 1 ? base + 40 : Math.max(0, base); // page 1 leaves headroom for the title
	}

	private static int menuTitleY() {
	    if (settingsMenu && settingsPage == 1) return settingsY0() - 12;
	    double screenY = Math.max(70, height / 5) + 3;
	    return (int) Math.round(height / 2.0 + (screenY - height / 2.0) / menuUiScale());
	}

	static final double SENS_MIN = Math.PI / 9000.0, SENS_MAX = Math.PI / 900.0;

	/** Slider position 0..1 -> sensitivity (log scale). */
	static double sensFromT(double t) {
		return SENS_MIN * Math.pow(SENS_MAX / SENS_MIN, Math.max(0, Math.min(1, t)));
	}

	/** Sensitivity -> slider position 0..1 (log scale). */
	static double tFromSens(double s) {
		s = Math.max(SENS_MIN, Math.min(SENS_MAX, s));
		return Math.log(s / SENS_MIN) / Math.log(SENS_MAX / SENS_MIN);
	}

	private void drawMenu(Graphics2D g) {
		// Main-menu settings already sit on the standard gray front-menu background.
		// Keep the dark overlay for the in-game pause/settings menu only.
		if (!(mainMenu && frontScreen == 3)) {
			g.setColor(new Color(18, 18, 20, 220));
			g.fillRect(0, 0, width, height);
		}
		g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
		g.setFont(pal(Font.BOLD, Math.max(28, Math.min(42, width / 24))));
		g.setColor(Color.WHITE);
		String title = quitConfirm ? "Save and Quit?" : settingsMenu ? (settingsPage == 1 ? "Extra Settings" : "General Settings") : "Paused!";
		FontMetrics fm = g.getFontMetrics();
		g.drawString(title, (width - fm.stringWidth(title)) / 2, menuTitleY());
		g.setFont(pal(Font.BOLD, Math.max(12, 15)));
		if (quitConfirm) {
			drawButton(g, menuRect(1), "Yes");
			drawButton(g, menuRect(2), "Cancel");
			return;
		}
		if (!settingsMenu) {
			drawButton(g, menuRect(1), "Return to Game");
			Rectangle settings = menuRect(2);
			settings.width = (settings.width - 8) / 2;
			drawButton(g, settings, "Settings");
			Rectangle teleport = menuRect(2);
			teleport.x += teleport.width / 2 + 4;
			teleport.width = (teleport.width - 8) / 2;
			drawButton(g, teleport, "Teleport");
			drawButton(g, menuRect(3), "Save and Quit");
		} else {
			int x0 = Math.max(24, width / 2 - 210), w = Math.min(420, width - 48);
			int y0 = settingsY0();
			int halfW = (w - 10) / 2;
			if (settingsPage == 1) {
				drawSlider(g,x0,y0,w,"Flight Speed",Math.log(Math.max(.01,Math.min(10,flight))/.01)/Math.log(1000),String.format(Locale.ROOT,"%.3f",flight));
				drawSlider(g,x0,y0+52,w,"Render Distance",(dist-16)/4080.0,dist+" ("+radius+(radius==1?" chunk":" chunks")+")");
				drawSlider(g,x0,y0+104,w,"FOV",(fov-FOV_MIN)/(FOV_MAX-FOV_MIN),String.format(Locale.ROOT,"%.2f°",fov));
				drawSlider(g,x0,y0+156,w,"Block Reach",(reach-2)/48.0,Integer.toString(reach));
				drawButton(g,new Rectangle(x0,y0+200,w,32),"Use Degrees: "+(degrees?"ON":"OFF"));
				drawExtraSettings(g, x0, w, y0 + 238);
				drawButton(g,new Rectangle(x0,y0+508,w,36),"Back to General Settings");
				return;
			}
			double sensClamped=Math.max(SENS_MIN,Math.min(SENS_MAX,sensitivity));
			double relativeSensitivity=sensClamped*(1800.0/Math.PI);
			drawSlider(g,x0,y0+18,w,"Mouse Sensitivity",tFromSens(sensClamped),"π / "+Math.round(Math.PI/sensClamped)+" (relative: "+String.format(Locale.ROOT,"%.2f",relativeSensitivity)+")");
			drawSlider(g,x0,y0+66,halfW,"Sound Volume",soundVolume/2.0,Math.round(soundVolume*100)+"%");
			drawSlider(g,x0+halfW+10,y0+66,halfW,"Music Volume",musicVolume/2.0,Math.round(musicVolume*100)+"%");
			drawButton(g,new Rectangle(x0,y0+108,halfW,30),"Sounds: "+(sound?"ON":"OFF"));
			drawButton(g,new Rectangle(x0+halfW+10,y0+108,halfW,30),"Music: "+(musicEnabled?"ON":"OFF"));
			drawButton(g,new Rectangle(x0,y0+150,w,30),"GUI Scale: "+Math.max(1,Math.min(3,scale)));
			drawButton(g,new Rectangle(x0,y0+202,w,48),"Extra Settings  >");
			drawButton(g,new Rectangle(x0,y0+260,w,36),"Apply & Close");
		}
	}

	private static void drawButton(Graphics2D g, Rectangle r, String text) { drawButton(g, r, text, 1); }

	private static void drawButton(Graphics2D g, Rectangle r, String text, float borderWidth) {
		final boolean front = mainMenu && (frontScreen == 2 || frontScreen == 3);
		g.setColor(front ? new Color(72,72,72,235) : new Color(65,65,72));
		g.fillRoundRect(r.x,r.y,r.width,r.height,9,9);
		g.setColor(front ? new Color(165,165,165) : new Color(130,130,140));
		Stroke old = g.getStroke(); g.setStroke(new BasicStroke(borderWidth)); g.drawRoundRect(r.x,r.y,r.width,r.height,9,9); g.setStroke(old);
		g.setColor(Color.WHITE); g.setFont(pal(Font.BOLD, 15)); FontMetrics fm=g.getFontMetrics();
		g.drawString(text,r.x+(r.width-fm.stringWidth(text))/2,r.y+(r.height+fm.getAscent()-fm.getDescent())/2 + 3);
	}

	private static void drawSlider(Graphics2D g,int x,int y,int w,String label,double t,String value) {
		drawSlider(g,x,y,w,label,t,value,false);
	}

	private static void drawSlider(Graphics2D g,int x,int y,int w,String label,double t,String value,boolean disabled) {
		g.setColor(disabled ? new Color(135,135,140) : Color.WHITE); g.drawString(label+": "+value,x,y+3);
		int sy=y+18; g.setColor(disabled ? new Color(65,65,68) : new Color(75,75,82)); g.fillRoundRect(x,sy,w,8,8,8);
		int px=x+(int)(Math.max(0,Math.min(1,t))*w);
		g.setColor(disabled ? new Color(100,100,104) : new Color(105,180,255)); g.fillRoundRect(x,sy,Math.max(1,px-x),8,8,8);
		g.setColor(disabled ? new Color(150,150,154) : Color.WHITE); g.fillOval(px-6,sy-4,16,16);
	}

	private void menuClick(int mx,int my) {
		// Convert screen coordinates into the menu graphics coordinate system.
		double guiScale = menuUiScale();
		mx = (int)Math.round(width / 2.0 + (mx - width / 2.0) / guiScale);
		my = (int)Math.round(height / 2.0 + (my - height / 2.0) / guiScale);
		if (quitConfirm) {
			if (menuRect(1).contains(mx,my)) { tasks.add(this::returnToMainMenu); }
			else if (menuRect(2).contains(mx,my)) quitConfirm=false;
			repaint(); return;
		}
		if (!settingsMenu) {
			if (menuRect(1).contains(mx, my)) {
				paused = false;
				settingsMenu = false;
				lock = true;
				mouseLookArmed = false;
				frame.setCursor(hidden);
				center();
			} else {
				Rectangle settings = menuRect(2);
				Rectangle teleport = menuRect(2);
				settings.width = (settings.width - 8) / 2;
				teleport.x += teleport.width / 2 + 4;
				teleport.width = (teleport.width - 8) / 2;
				if (settings.contains(mx, my)) {
					settingsMenu = true;
					settingsPage = 0;
				} else if (teleport.contains(mx, my)) {
					openModifyDialog();
				} else if (menuRect(3).contains(mx, my)) {
					quitConfirm = true;
				}
			}
		} else {
			int x0=Math.max(24,width/2-210), w=Math.min(420,width-48), y0=settingsY0();
			int halfW=(w-10)/2;
			if(settingsPage==1) {
				if(my>=y0+18&&my<=y0+42) flight=.01*Math.pow(1000,Math.max(0,Math.min(1,(mx-x0)/(double)w)));
				else if(my>=y0+70&&my<=y0+94) requestDist(16+(int)Math.round(Math.max(0,Math.min(1,(mx-x0)/(double)w))*255)*16);
				else if(my>=y0+110&&my<=y0+134) setFov(FOV_MIN+(FOV_MAX-FOV_MIN)*Math.max(0,Math.min(1,(mx-x0)/(double)w)));
				else if(my>=y0+166&&my<=y0+190) reach=(byte)(2+Math.round(Math.max(0,Math.min(1,(mx-x0)/(double)w))*48));
				else if(my>=y0+200&&my<=y0+232) degrees=!degrees;
				else if(my>=y0+508&&my<=y0+544){ if(rgbEditChannel!=-1)applyRgbEdit(); settingsPage=0; }
				else extraSettingsClick(mx,my,x0,w,y0+238);
			} else {
				if(my>=y0+18&&my<=y0+42) sensitivity=sensFromT((mx-x0)/(double)w);
				else if(my>=y0+66&&my<=y0+90) {if(mx<x0+halfW) soundVolume=2*Math.max(0,Math.min(1,(mx-x0)/(double)halfW));else musicVolume=2*Math.max(0,Math.min(1,(mx-(x0+halfW+10))/(double)halfW));}
				else if(my>=y0+108&&my<=y0+138) {if(mx<x0+halfW) sound=!sound;else musicEnabled=!musicEnabled;}
				else if(my>=y0+150&&my<=y0+180) scale=(byte)(Math.max(1,Math.min(3,scale))%3+1);
				else if(my>=y0+202&&my<=y0+250) settingsPage=1;
				else if(my>=y0+260&&my<=y0+296) {if(rgbEditChannel>=0)applyRgbEdit();settingsMenu=false;settingsPage=0;}
			}
		}
		repaint();
	}

	private void menuSliderDrag(int mx, int my) {
		final boolean create = mainMenu && frontScreen == 2;
		if ((!paused && !(mainMenu && frontScreen==3)) || (!settingsMenu && !(mainMenu && frontScreen==3)) || menuSliderTarget < 0) return;
		{ double s = mainMenu && frontScreen == 3 ? menuUiScale() : (paused ? Math.max(1, scale) : 1.0); mx = (int)Math.round(width / 2.0 + (mx - width / 2.0) / s); my = (int)Math.round(height / 2.0 + (my - height / 2.0) / s); }
		int x0=Math.max(24,width/2-210), w=Math.min(420,width-48);
		if (create) { int[] gm = createGeom(); x0 = gm[0]; w = gm[1]; } else { x0 = Math.max(24,width/2-210); w = Math.min(420,width-48); }
		if (menuSliderTarget == 5) { reach=(byte)(2+Math.round(Math.max(0,Math.min(1,(mx-x0)/(double)w))*48));
		} else if (menuSliderTarget == 6) { setFov(FOV_MIN+(FOV_MAX-FOV_MIN)*Math.max(0,Math.min(1,(mx-x0)/(double)w)));
		} else if (menuSliderTarget == 7) { if (!survival) power=(byte)(1+Math.round(Math.max(0,Math.min(1,(mx-x0)/(double)w))*126));
		} else if (menuSliderTarget == 8) { AO_STRENGTH=Math.round(Math.max(0,Math.min(1,(mx-x0)/(double)w))*100)/100.0;
		} else if (menuSliderTarget == 0) {
			double t=Math.max(0,Math.min(1,(mx-x0)/(double)w)); flight=.01*Math.pow(1000,t);
		} else if (menuSliderTarget == 1) {
			double t=Math.max(0,Math.min(1,(mx-x0)/(double)w)); requestDist(16+(int)Math.round(t*255)*16);
		} else if (menuSliderTarget == 2) {
			sensitivity=sensFromT((mx-x0)/(double)w);
		} else if (menuSliderTarget == 3 || menuSliderTarget == 4) {
			int halfW=(w-10)/2;
			double t = menuSliderTarget == 3 ? (mx-x0)/(double)halfW : (mx-(x0+halfW+10))/(double)halfW;
			t=Math.max(0,Math.min(1,t));
			if(menuSliderTarget==3) soundVolume=2*t; else musicVolume=2*t;
		} else return;
		repaint();
	}

	private void applyRgbEdit() {
		try {
			if (rgbEditChannel == -2) {
				String hex=rgbEdit.trim().replace("#","");
				if(hex.length()==3) hex=""+hex.charAt(0)+hex.charAt(0)+hex.charAt(1)+hex.charAt(1)+hex.charAt(2)+hex.charAt(2);
				int c=Integer.parseInt(hex,16);
				red=((c>>16)&255)/255.0; green=((c>>8)&255)/255.0; blue=(c&255)/255.0;
			} else {
				double v=Math.max(0,Math.min(1,Double.parseDouble(rgbEdit)));
				if(rgbEditChannel==0)red=v; else if(rgbEditChannel==1)green=v; else if(rgbEditChannel==2)blue=v;
			}
		} catch(Exception ignored) {}
		rgbEditChannel=-1; rgbEdit="";
	}

	/** Main thread only. */
	private static void update() {
		int wd = width;
		if (wd != fovWidth) {
			fovWidth = wd;
			scale = (byte) autoGuiScale(wd);
			setFov(autoFov(wd));
		}
		int newResX = Math.max(1, (int) ((width / 8.0) * Math.pow(2, detail)));
		int newResY = Math.max(1, (int) ((height / 8.0) * Math.pow(2, detail)));
		if (resX != newResX || resY != newResY || buffer.length != newResX * newResY) {
			allocateBuffers(newResX, newResY);
			resX = newResX;
			resY = newResY;
		}
		Arrays.fill(buffer, 0);
	}

	// ------------------------------------------------------------------ save / load

	private static void chooser(Component component) {
		if (scale <= 1)
	        return;

	    Font font = component.getFont();

	    if (font != null) {
	        component.setFont(font.deriveFont(font.getSize2D() * scale));
	    }

	    if (component instanceof Container) {
	        Container container = (Container) component;
	        for (Component child : container.getComponents()) {
	            chooser(child);
	        }
	    }

	    if (component instanceof JFileChooser) {
	        JFileChooser chooser = (JFileChooser) component;
	        Dimension size = chooser.getPreferredSize();

	        chooser.setPreferredSize(new Dimension(
	            size.width,
	            (int) (size.height * 1.5)
	        ));
	    }
	}

	private static Map<Long, Object> changedChunkSnapshot() {
		Map<Long, Object> chunks = new TreeMap<>();
		for (Map.Entry<Long, Object> e : savedChunks.entrySet())
			chunks.put(e.getKey(), e.getValue() instanceof Octree ? ((Octree) e.getValue()).frozen() : e.getValue());
		for (int slot = 0; slot < world.keys.length; slot++) {
			long key = world.keys[slot];
			if (key != World.NONE && world.user[slot])
				chunks.put(key, world.data[slot] == null ? EMPTY : world.data[slot].frozen());
		}
		return chunks;
	}

	private static final class SaveSnapshot {
		final File file;
		final Map<Long, Object> chunks;
		final long pxi, pyi, pzi, sxi, syi, szi;
		final double pxf, pyf, pzf, sxf, syf, szf, pyaw, ppitch, amplitude, fr, fg, fb;
		final short renderDistance;
		final long worldTime;
		final boolean worldCaves, worldTerrain3D, worldClassic, worldXor, flight;
		final boolean sSurvival; final double sFlightSpeed; final int sHealth; final byte[][] sInvId; final int[][] sInvCount;
		SaveSnapshot(File file, Map<Long, Object> chunks) {
			this.file = file; this.chunks = chunks;
			pxi = x.getIntegerPart(); pxf = x.getFractionalPart();
			pyi = y.getIntegerPart(); pyf = y.getFractionalPart();
			pzi = z.getIntegerPart(); pzf = z.getFractionalPart();
			sxi = worldSpawnX.getIntegerPart(); sxf = worldSpawnX.getFractionalPart();
			syi = worldSpawnY.getIntegerPart(); syf = worldSpawnY.getFractionalPart();
			szi = worldSpawnZ.getIntegerPart(); szf = worldSpawnZ.getFractionalPart();
			pyaw = yaw; ppitch = pitch; renderDistance = dist; worldTime = time; flight = fly;
			worldCaves = caves; worldTerrain3D = terrain3D; amplitude = amp; fr = red; fg = green; fb = blue;
			worldClassic = classic; worldXor = xor;
			sSurvival = Nexus.survival; sFlightSpeed = Nexus.flight; sHealth = Nexus.health;
			sInvId = copyIds(Nexus.invId); sInvCount = copyCounts(Nexus.invCount);
		}
	}

	private static void doSave(File file) {
		persistentStorage = true;
		activeSaveFile = file;
		if (!saveInProgress.compareAndSet(false, true)) {
			// Never silently discard a save request while another write is running.
			requestedSaveFile = file;
			saveRequested = true;
			return;
		}
		flushDirty();
		// Snapshot includes player position, rotation, time, settings, and changed chunks.
		SaveSnapshot snapshot = new SaveSnapshot(file, changedChunkSnapshot());
		savePool.execute(() -> {
			try { writeSave(snapshot); }
			finally { saveInProgress.set(false); }
		});
	}
	/** Best-effort final save for window close, System.exit, and other normal JVM shutdowns. */
	private static void saveOnShutdown() {
		if (shutdownSaveStarted) return;
		shutdownSaveStarted = true;
		File file = activeSaveFile;
		if (!persistentStorage || file == null) return; // no chosen world file to save to
		try {
			// Let an autosave already in progress finish before writing the final snapshot.
			long deadline = System.currentTimeMillis() + 15_000L;
			while (saveInProgress.get() && System.currentTimeMillis() < deadline)
				Thread.sleep(25L);
			SaveSnapshot snapshot = new SaveSnapshot(file, changedChunkSnapshot());
			writeSave(snapshot); // synchronous: shutdown hooks must finish before the JVM exits
		} catch (Throwable t) {
			System.err.println("Final world save failed: " + t);
			t.printStackTrace();
		}
	}

	private static void writeSave(SaveSnapshot s) {
		synchronized (SAVE_LOCK) {
		writeSaveLocked(s);
		}
	}

	private static void writeSaveLocked(SaveSnapshot s) {
		Path target = s.file.toPath();
		Path tmp = target.resolveSibling(target.getFileName() + ".tmp");
		try {
			try (DataOutputStream out = new DataOutputStream(new BufferedOutputStream(Files.newOutputStream(tmp), 1 << 16))) {
				out.writeInt(MAGIC);
				out.writeLong(s.pxi); out.writeDouble(s.pxf); out.writeLong(s.pyi); out.writeDouble(s.pyf); out.writeLong(s.pzi); out.writeDouble(s.pzf);
				out.writeDouble(s.pyaw); out.writeDouble(s.ppitch); out.writeShort(s.renderDistance);
				out.writeLong(s.worldTime); out.writeBoolean(s.flight); out.writeBoolean(s.worldCaves); out.writeBoolean(s.worldTerrain3D);
				out.writeDouble(s.amplitude); out.writeDouble(s.fr); out.writeDouble(s.fg); out.writeDouble(s.fb);
				out.writeBoolean(s.worldClassic); out.writeBoolean(s.worldXor);
				out.writeBoolean(s.sSurvival); out.writeDouble(s.sFlightSpeed); out.writeInt(s.sHealth);
				for (int p = 0; p < INV_PAGES; p++)
					for (int i = 0; i < INV_SLOTS; i++) { out.writeByte(s.sInvId[p][i]); out.writeInt(s.sInvCount[p][i]); }
				out.writeInt(s.chunks.size());
				Deflater def = new Deflater(Deflater.BEST_SPEED);
				try {
					DeflaterOutputStream z = new DeflaterOutputStream(out, def, 1 << 16);
					DataOutputStream cd = new DataOutputStream(z);
					for (Map.Entry<Long, Object> e : s.chunks.entrySet()) {
						byte[] blob = blobOf(e.getValue());
						cd.writeLong(e.getKey()); cd.writeInt(blob.length); cd.write(blob);
					}
					// Optional trailer within the compressed payload stores the actual world spawn.
					cd.writeInt(0x5350574E); // SPWN
					cd.writeLong(s.sxi); cd.writeDouble(s.sxf); cd.writeLong(s.syi); cd.writeDouble(s.syf); cd.writeLong(s.szi); cd.writeDouble(s.szf);
					cd.flush(); z.finish();
				} finally { def.end(); }
			}
			// Keep a small last-known-good copy before replacing the primary save.
			// If the primary write is interrupted later, this backup remains recoverable.
			if (Files.isRegularFile(target)) {
				Path backup = target.resolveSibling(target.getFileName() + ".bak");
				try { Files.copy(target, backup, StandardCopyOption.REPLACE_EXISTING); }
				catch (IOException backupError) { System.err.println("Could not refresh world backup: " + backupError); }
			}
			try { Files.move(tmp, target, StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE); }
			catch (AtomicMoveNotSupportedException ex) { Files.move(tmp, target, StandardCopyOption.REPLACE_EXISTING); }
		} catch (Exception e) {
			e.printStackTrace();
			try { Files.deleteIfExists(tmp); } catch (IOException ignored) {}
			SwingUtilities.invokeLater(() -> JOptionPane.showMessageDialog(frame, "Failed to save world:\n" + e.getMessage()));
		}
	}

	private static long blockAtPosition(SplitDecimal p, double offset) {
		return p.getIntegerPart() + (long)Math.floor(p.getFractionalPart() + offset);
	}

	/** Checks the saved, player-edited voxels at the twelve collision samples around a spawn. */
	private static boolean savedSpawnObstructed(SplitDecimal sx, SplitDecimal sy, SplitDecimal sz) {
		Map<Long, Octree> decoded = new HashMap<>();
		for (byte c=0;c<12;c++) {
			long bx=blockAtPosition(sx,(c&1)*0.6-0.3);
			long by=blockAtPosition(sy,((c>>2)-1)*0.8+0.65);
			long bz=blockAtPosition(sz,(c>>1&1)*0.6-0.3);
			long key=World.key(bx>>SHIFT,by>>SHIFT,bz>>SHIFT);
			Object saved=savedChunks.get(key);
			if(saved==null) continue; // unedited terrain was already accounted for by the saved ground height
			Octree tree=decoded.get(key);
			if(!decoded.containsKey(key)){tree=restore(saved);decoded.put(key,tree);}
			if(tree!=null && tree.get((byte)(bx&MASK),(byte)(by&MASK),(byte)(bz&MASK))!=AIR) return true;
		}
		return false;
	}

	private static void repairSavedSpawnIfBlocked() {
		if (!savedSpawnObstructed(worldSpawnX,worldSpawnY,worldSpawnZ)) return;
		// Try the eight nearby directions at roughly sixteen blocks, preserving the world.
		for (byte radius=16; radius<=16; radius+=16) {
			for (byte ring=0;ring<8;ring++) {
				double a=ring*Math.PI/4.0;
				SplitDecimal sx=copyOf(worldSpawnX), sz=copyOf(worldSpawnZ);
				shift(sx,Math.round(Math.cos(a)*radius)); shift(sz,Math.round(Math.sin(a)*radius));
				SplitDecimal sy=new SplitDecimal(); sy.setValue(estimateGround(floorOf(sx),floorOf(sz)));
				if (!savedSpawnObstructed(sx,sy,sz)) { worldSpawnX.set(sx);worldSpawnY.set(sy);worldSpawnZ.set(sz); saveRequested=true;requestedSaveFile=activeSaveFile;return; }
			}
		}
		// Last resort: choose a new random coordinate in the full 65,536-wide range.
		Random random=new Random();
		for(byte i=0;i<32;i++) {
			SplitDecimal sx=new SplitDecimal(random.nextInt(65536)-32768+0.5), sz=new SplitDecimal(random.nextInt(65536)-32768+0.5);
			SplitDecimal sy=new SplitDecimal(); sy.setValue(estimateGround(floorOf(sx),floorOf(sz)));
			if(!savedSpawnObstructed(sx,sy,sz)){worldSpawnX.set(sx);worldSpawnY.set(sy);worldSpawnZ.set(sz);saveRequested=true;requestedSaveFile=activeSaveFile;return;}
		}
	}

	private static void doLoad(File file) {
		fly = false; // Turn off title-screen flight before loading any world data.
		worldLoading = true;
		worldLoadReadyAt = 0L;
		velX = velY = velZ = 0;
		mouseLookArmed = false;
		final int MAX_BLOB = 2 * VOL + 16; // worst case: alternating blocks, 2 bytes each
		try (DataInputStream in = new DataInputStream(new BufferedInputStream(Files.newInputStream(file.toPath()), 1 << 16))) {
			int magic = in.readInt();
			if (magic != MAGIC) {
				worldLoading = false; worldLoadReadyAt = 0L;
				JOptionPane.showMessageDialog(frame, "Unsupported file (older format, or not a Nexus save)");
				return;
			}
			SplitDecimal nx, ny, nz;
			nx = new SplitDecimal(in.readLong(), in.readDouble());
			ny = new SplitDecimal(in.readLong(), in.readDouble());
			nz = new SplitDecimal(in.readLong(), in.readDouble());
			double nYaw = in.readDouble(), nPitch = in.readDouble();
			short nDist = in.readShort();
			long nTime = in.readLong();
			boolean nFly = in.readBoolean(); boolean nCaves = in.readBoolean(), nT3 = in.readBoolean();
			double nAmp = in.readDouble(), nRed = in.readDouble(), nGreen = in.readDouble(), nBlue = in.readDouble();
			boolean nClassic = in.readBoolean(), nXor = in.readBoolean();
			boolean nSurvival = in.readBoolean(); double nFlightSpeed = in.readDouble(); int nHealth = in.readInt();
			byte[][] nInvId = new byte[INV_PAGES][INV_SLOTS]; int[][] nInvCount = new int[INV_PAGES][INV_SLOTS];
			for (int p = 0; p < INV_PAGES; p++)
				for (int i = 0; i < INV_SLOTS; i++) {
					byte id = in.readByte(); int cnt = in.readInt();
					if (id <= 0 || id >= BLOCK_COUNT || cnt <= 0) { id = AIR; cnt = 0; }
					nInvId[p][i] = id; nInvCount[p][i] = Math.min(cnt, STACK_MAX);
				}

			int count = in.readInt();
			if (count < 0)
				throw new IOException("Invalid chunk count: " + count);
			Map<Long, byte[]> loaded = new HashMap<>();
			try (DataInputStream cd = new DataInputStream(new InflaterInputStream(in))) {
				for (int i = 0; i < count; i++) {
					long key = cd.readLong();
					int len = cd.readInt();
					if (len < 0 || len > MAX_BLOB)
						throw new IOException("Invalid chunk length: " + len);
					byte[] blob = new byte[len];
					cd.readFully(blob);
					loaded.put(key, len == 0 ? EMPTY : blob);
				}
				try {
					if (cd.readInt() == 0x5350574E) {
						worldSpawnX.set(new SplitDecimal(cd.readLong(), cd.readDouble()));
						worldSpawnY.set(new SplitDecimal(cd.readLong(), cd.readDouble()));
						worldSpawnZ.set(new SplitDecimal(cd.readLong(), cd.readDouble()));
					} else { worldSpawnX.set(nx); worldSpawnY.set(ny); worldSpawnZ.set(nz); }
				} catch (EOFException oldFormat) { worldSpawnX.set(nx); worldSpawnY.set(ny); worldSpawnZ.set(nz); }
			}

			x.set(nx); y.set(ny); z.set(nz);
			prevX.set(x); prevY.set(y); prevZ.set(z);
			yaw = nYaw;
			pitch = nPitch;
			time = nTime;
			fly = nFly;
			caves = nCaves;
			terrain3D = nT3;
			amp = nAmp;
			red = nRed;
			green = nGreen;
			blue = nBlue;
			classic = nClassic;
			xor = nXor;
			applySurvivalState(nSurvival, nFlightSpeed, nHealth, nInvId, nInvCount);
			textures();
			velX = velY = velZ = 0;

			setDist(nDist);
			reloadChunks(false);
			savedChunks.putAll(loaded);
			for (long k : loaded.keySet())
				userTopY = Math.min(userTopY, World.unpackY(k) * SIZE);
			activeSaveFile = file;
			persistentStorage = true;
			repairSavedSpawnIfBlocked();
			mainMenu = false;
			frame.setCursor(hidden);
			frontScreen = 0;
			lock = true; focus = true;
			lastPersistentSave = System.currentTimeMillis();
			needGround = false;
			prevX.set(x); prevY.set(y); prevZ.set(z);
			if (dead) die();   // saved while dead -> shows the death screen again
		} catch (Exception e) {
			worldLoading = false; worldLoadReadyAt = 0L;
			e.printStackTrace();
			JOptionPane.showMessageDialog(frame, "Failed to load world:\n" + e.getMessage());
		}
	}

	private static byte[] encode(byte[] data) {
		byte[] out = SAVE_ENC.get();
		int n = 0, i = 0;
		final int len = data.length;
		while (i < len) {
			byte v = data[i];
			int j = i + 1;
			while (j < len && data[j] == v)
				j++;
			int run = j - i;
			out[n++] = v;
			while (run >= 0x80) {
				out[n++] = (byte) (run | 0x80);
				run >>>= 7;
			}
			out[n++] = (byte) run;
			i = j;
		}
		return Arrays.copyOf(out, n);
	}

	// ------------------------------------------------------------------ input

	private static void center() {
		if (robot == null) {
			try {
				robot = new Robot();
			} catch (AWTException e) {
				e.printStackTrace();
			}
		}
		if (robot != null && frame.isShowing()) {
			Point center = new Point(frame.getWidth() / 2, frame.getHeight() / 2);
			SwingUtilities.convertPointToScreen(center, frame);
			robot.mouseMove(center.x, center.y);
		}
	}

	private static void centered(Graphics2D g,String text,int cx,int y) { g.drawString(text,cx-g.getFontMetrics().stringWidth(text)/2,y); }

	static final int MODIFY_H = 290;

	private void drawModifyUi(Graphics2D g) {
	    try {
	        g.setColor(new Color(0,0,0,170)); g.fillRect(0,0,width,height);
	        int w = Math.min(520, width - 32), h = MODIFY_H, x = (width-w)/2, y = (height-h)/2;
	        g.setColor(new Color(27,28,33,245)); g.fillRoundRect(x,y,w,h,16,16);
	        g.setColor(new Color(115,125,145)); g.drawRoundRect(x,y,w,h,16,16);
	        g.setFont(pal(Font.BOLD,22)); g.setColor(Color.WHITE); centered(g,"Teleport",width/2,y+34);
	        String[] labels = {"X Coordinate", "Y Coordinate", "Z Coordinate", "Time", "Flight Speed"};
	        g.setFont(pal(Font.PLAIN,14));
	        int rowY = y+58;
	        for (int i=0;i<labels.length;i++) {
	            int yy=rowY+i*34; g.setColor(new Color(220,224,232)); g.drawString(labels[i]+":",x+28,yy+20);
	            Rectangle field = new Rectangle(x+190,yy,w-220,27);
	            g.setColor(i==modifyFocus?new Color(65,86,112):new Color(45,47,54)); g.fillRoundRect(field.x,field.y,field.width,field.height,6,6);
	            g.setColor(i==modifyFocus?new Color(120,190,255):new Color(90,93,104)); Stroke oldFieldStroke=g.getStroke(); g.setStroke(new BasicStroke(1.0f)); g.drawRoundRect(field.x,field.y,field.width,field.height,6,6); g.setStroke(oldFieldStroke);
	            String val=modifyValues[i]==null?"":modifyValues[i];
	            g.setFont(pal(Font.PLAIN,14)); FontMetrics fm=g.getFontMetrics(); int baseline=field.y+18, tx=field.x+9;
	            if(i==modifyFocus){int a=Math.max(0,Math.min(val.length(),Math.min(modifyCaret,modifyAnchor))), b=Math.max(0,Math.min(val.length(),Math.max(modifyCaret,modifyAnchor)));
	                if(a!=b){int sx=tx+fm.stringWidth(val.substring(0,a)), ex=tx+fm.stringWidth(val.substring(0,b)); g.setColor(new Color(75,112,165)); g.fillRect(sx,field.y+4,Math.max(1,ex-sx),field.height-8);}
	            }
	            g.setColor(Color.WHITE); g.drawString(val,tx,baseline);
	            if(i==modifyFocus && (System.currentTimeMillis()%1000)<550){int cx=tx+fm.stringWidth(val.substring(0,Math.max(0,Math.min(val.length(),modifyCaret)))); g.setColor(Color.WHITE); Stroke oldStroke=g.getStroke(); g.setStroke(new BasicStroke(0.5f)); g.drawLine(cx,field.y+5,cx,field.y+field.height-5); g.setStroke(oldStroke);}
	        }
	        int by = y + h - 52;
	        drawButton(g,new Rectangle(x+20,by,(w-48)/2,32),"Apply & Teleport",0.8f);
	        drawButton(g,new Rectangle(x+28+(w-48)/2,by,(w-48)/2,32),"Cancel",0.8f);
	    } finally { g.dispose(); }
	}

	private void modifyUiClick(int mx,int my) {
	    int w=Math.min(520,width-32),h=MODIFY_H,x=(width-w)/2,y=(height-h)/2,rowY=y+58;
	    for(int i=0;i<modifyValues.length;i++){ Rectangle r=new Rectangle(x+190,rowY+i*34,w-220,27); if(r.contains(mx,my)){modifyFocus=i; String val=modifyValues[i]==null?"":modifyValues[i]; FontMetrics fm=getFontMetrics(pal(Font.PLAIN,14)); int target=mx-(r.x+9); modifyCaret=0; while(modifyCaret<val.length() && fm.stringWidth(val.substring(0,modifyCaret+1))<target) modifyCaret++; modifyAnchor=modifyCaret; repaint();return;} }
	    int by=y+h-52;
	    if(new Rectangle(x+20,by,(w-48)/2,32).contains(mx,my)) { applyModifyValues(); return; }
	    else if(new Rectangle(x+28+(w-48)/2,by,(w-48)/2,32).contains(mx,my)) { modifyUi=false;dialogOpen=false;repaint();return; }
	    repaint();
	}

	private void openModifyDialog() {
		if (survival) return;
	    modifyUi = true; dialogOpen = true; lock = false;
	    frame.setCursor(Cursor.getDefaultCursor());
	    velX = velY = velZ = 0;
	    modifyValues = new String[] { coordStr(x, false), coordStr(y, true), coordStr(z, false), Long.toString(time), Double.toString(flight) };
	    modifyFocus = 0; modifyCaret = modifyValues[0].length(); modifyAnchor = modifyCaret;
	    synchronized (input) { input.clear(); }
	    repaint();
	}

	private void applyModifyValues() {
	    try {
	        final SplitDecimal nx = parseCoord(modifyValues[0]), nz = parseCoord(modifyValues[2]);
	        final SplitDecimal ny = new SplitDecimal();
	        parseCoord(modifyValues[1]).negate(ny); // displayed Y is -y
	        final long nt = Long.parseLong(modifyValues[3]);
	        final double nf = Double.parseDouble(modifyValues[4]);
	        if (!Double.isFinite(nf) || nf <= 0)
	            throw new NumberFormatException("flight speed must be finite and positive");
	        tasks.add(() -> {
	            boolean movedXZ = !nx.equals(x) || !nz.equals(z);
	            time = nt; flight = nf;
	            moveTo(nx, ny, nz, movedXZ ? !fly : needGround);
	        });
	        modifyUi = false; dialogOpen = false; repaint();
	    } catch (NumberFormatException ex) { say("Invalid value: " + ex.getMessage()); }
	}

	// ------------------- feature locator (N = cycle target, B = teleport)
	static final String[] LOC_NAMES = {
		    "Moss Basin",
		    "Snow Basin",
		    "Moss Cave",
		    "Snow Cave",
		    "Obsidian Cave",
		    "Crystal Cave",
		    "Basalt Cave",
		    "Snowy Biome",
		    "Icy Biome",
		    "Desert Biome",
		    "Plains Biome",
		    "Autumn Forest",
		    "Menger Sponge"
		};
	static int locTarget;
	static volatile String locMsg = "";
	static volatile long locMsgTime;
	private static final AtomicBoolean locBusy = new AtomicBoolean();

	private static void say(String s) {
		locMsg = s;
		locMsgTime = System.currentTimeMillis();
	}

	/** Same width curve as carveCaves. */
	private static double caveWidthAt(double wy) {
		double t = Math.max(0.0, Math.min(1.0, (wy - CAVE_SURFACE_Y) / (CAVE_FULL_DENSITY_Y - CAVE_SURFACE_Y)));
		t = t * t * (3.0 - 2.0 * t);
		return CAVE_SURFACE_WIDTH + (CAVE_W - CAVE_SURFACE_WIDTH) * t;
	}

	/** True if the two cave noise fields are both near zero here (inside a tunnel, with some margin). */
	private static boolean caveAir(double x, double y, double z) {
		double lim = caveWidthAt(y) * 0.8;
		double a = noise3(x * CAVE_XZ, y * CAVE_Y, z * CAVE_XZ, 0x2A) * 2 - 1;
		if (Math.abs(a) > lim)
			return false;
		double b = noise3(x * CAVE_XZ, y * CAVE_Y, z * CAVE_XZ, 0x6B) * 2 - 1;
		return Math.abs(b) <= lim;
	}

	/** True if no higher-priority cave biome claims this spot (same order carveCaves uses). */
	private static boolean dominant(int biome, long x, long y, long z) {
		for (int b : CB_ORDER) {
			if (b == biome)
				return true;
			if (zoneAt(b, x, y, z) > 0)
				return false;
		}
		return false;
	}

	/** Scans one column for a point that is inside a tunnel AND inside the biome zone. */
	private static double[] caveProbe(int biome, long wx, long wz) {
		long y0, y1;
		if (biome >= CB_OBSIDIAN) { // magma layer only
			y0 = (long) (TBASE + layer2(wx, wz)) + 12;
			y1 = y0 + 300;
		} else {
			if (biome == CB_SNOW && noise(wx / 512.0, wz / 512.0) <= 1.4)
				return null; // snow caves only under snowy biomes
			y0 = (long) MOSS_Y0 + 8;
			y1 = (long) MOSS_Y3 - 8;
		}
		for (long y = y0; y <= y1; y += 4)
			if (zoneAt(biome, wx, y, wz) > 0.3 && dominant(biome, wx, y, wz) && caveAir(wx + 0.5, y + 0.5, wz + 0.5))
				return new double[] { wx + 0.5, y + 0.5, wz + 0.5 };
		return null;
	}

	private static double[] surfaceProbe(int t, long wx, long wz) {
	    double n = noise(wx / 512.0, wz / 512.0);

	    boolean ok = t == 7 ? n > 1.4 && n < 1.85
	             : t == 8 ? n > 1.85
	             : t == 9 ? n < 0.65
	             : t == 10 ? n > 0.8 && n < 1.3
	             : t == 11 && isAutumnForest(wx, wz, n);

	    return ok ? new double[] { wx + 0.5, 0, wz + 0.5 } : null;
	}

	/** One grid cell (gx, gz) for the given target; returns a world {x, y, z} or null. */
	private static double[] probe(int t, long gx, long gz, int cell) {
		if (t == 12) {
		    MengerSite s = mengerSite(gx, gz);
		    return s.valid ? new double[] { s.ax + 0.5, s.surface - s.size / 2.0 + 0.5, s.az + 0.5 } : null;
		}
	    if (t < 2) {
	        double[] b = basinAt(gx, gz);
	        int want = t == 0 ? CB_MOSS : CB_SNOW;

	        return b != null && (int) b[6] == want
	            ? new double[] { b[0], b[1], b[2] }
	            : null;
	    }

	    long wx = gx * cell + cell / 2;
	    long wz = gz * cell + cell / 2;

	    // Targets 2–6 are caves, including Basalt Cave at index 6.
	    if (t < 7)
	        return caveProbe(t - 1, wx, wz);

	    // Targets 7+ are surface biomes.
	    return surfaceProbe(t, wx, wz);
	}

	static final double LOCATE_RADIUS = 5000;

	/** Rejects farlands garbage (non-finite or out-of-band basin heights). */
	private static boolean validHit(int t, double[] h) {
	    if (!Double.isFinite(h[0]) || !Double.isFinite(h[1]) || !Double.isFinite(h[2])) return false;
	    return t >= 2 || (h[1] >= TBASE + 40 && h[1] <= BASIN_MAX_Y + 64);
	}

	/** Square rings of cells around the player, stopping once no farther ring can hold a closer hit. */
	private static double[] search(int t, long px, long pz) {
	    final int cell = t < 2 ? BASIN_CELL : t < 7 ? 32 : t == 12 ? MENGER_CELL : 64;
	    final int rings = (int) Math.ceil(LOCATE_RADIUS / cell);
	    final long cx = Math.floorDiv(px, (long) cell), cz = Math.floorDiv(pz, (long) cell);
	    double[] best = null;
	    double bestD2 = LOCATE_RADIUS * LOCATE_RADIUS;
	    for (int r = 0; r <= rings; r++) {
	        double ringMin = Math.max(0, r - 1) * (double) cell;
	        if (best != null && ringMin * ringMin > bestD2) break;
	        for (long dx = -r; dx <= r; dx++)
	            for (long dz = -r; dz <= r; dz += (Math.abs(dx) == r || r == 0) ? 1 : 2 * r) {
	                double[] hit = probe(t, cx + dx, cz + dz, cell);
	                if (hit == null || !validHit(t, hit)) continue;
	                double ddx = hit[0] - px, ddz = hit[2] - pz, d2 = ddx * ddx + ddz * ddz;
	                if (d2 < bestD2) { bestD2 = d2; best = hit; }
	            }
	    }
	    return best;
	}

	static volatile long warmUntil;
	/** True for a while after a world (re)load: Render time-slices its expensive lighting. */
	static boolean lightWarming() { return System.currentTimeMillis() < warmUntil; }

	/** Main thread only. Drops every loaded chunk and any in-flight generation so nothing stale survives. */
	static void reloadChunks(boolean keepEdits) {
		MENGER_SITES.clear();
		lightVer++;
		if (inFlight != null) {
			for (Future<Octree> f : inFlight.futures) f.cancel(true);
			inFlight = null;
		}
		if (keepEdits) flushDirty(); else clearSaved();
		pendingWrites.clear(); pendingCount = 0;
		chunkCache.clear(); cacheBytes = 0;
		world.clear(); // bumps the epoch: any batch still running is discarded
		featureQueue.clear();
		featureEpoch = world.epoch;
		lcx = Long.MIN_VALUE; lcy = lcz = 0;
		caveCheckX = Long.MIN_VALUE; caveSnap = true; caveTarget = 0;
		warmUntil = System.currentTimeMillis() + 1000L;
		chunkDirty = true;
		Particles.clear();
	}

	static void moveTo(SplitDecimal nx, SplitDecimal ny, SplitDecimal nz, boolean ground) {
		double dx = diff(nx, x), dy = diff(ny, y), dz = diff(nz, z);
		double far = TELEPORT_RELOAD_RADII * radius * SIZE;
		boolean reload = dx * dx + dy * dy + dz * dz > far * far;
		x.set(nx); y.set(ny); z.set(nz);
		prevX.set(x); prevY.set(y); prevZ.set(z);
		velX = velY = velZ = 0;
		Particles.clear();
		if (reload) reloadChunks(true);
		else cleanupOldChunks(true); // unload everything now outside the new render sphere
		chunkDirty = true;
		needGround = ground;
	}

	/** Used by the locator, whose results are plain doubles. */
	static void moveTo(double nx, double ny, double nz, boolean ground) {
		moveTo(new SplitDecimal(nx), new SplitDecimal(ny), new SplitDecimal(nz), ground);
	}

	private static void teleport(double[] p, boolean ground) {
		tasks.add(() -> moveTo(p[0], p[1], p[2], ground));
	}

	private static void locate(int t) {
		if (survival) return;
		if (t < 7 && !caves) {
			say("Enable caves first (F10)");
			return;
		}
		if (!locBusy.compareAndSet(false, true))
			return;
		final long px = floorOf(x), pz = floorOf(z);
		say("Searching for " + LOC_NAMES[t] + "...");
		Thread th = new Thread(() -> {
			try {
				double[] hit = search(t, px, pz);
				if (hit == null) {
					say(LOC_NAMES[t] + ": none found nearby");
				} else {
					say(String.format("%s at (%.0f, %.0f, %.0f)", LOC_NAMES[t], hit[0], -hit[1] + 0.0, hit[2]));
					teleport(hit, t >= 7);
				}
			} finally {
				locBusy.set(false);
			}
		}, "nexus-locate");
		th.setDaemon(true);
		th.start();
	}

	static void trimPending() {
		Iterator<Map.Entry<Long, LinkedHashSet<Long>>> it = pendingWrites.entrySet().iterator();
		while (it.hasNext() && pendingCount > PENDING_MAX * 3 / 4) {
			pendingCount -= it.next().getValue().size();
			it.remove();
		}
	}

	static void dropPending(long key) {
		LinkedHashSet<Long> s = pendingWrites.remove(key);
		if (s != null) pendingCount -= s.size();
	}

	/** floor(p) as a block coordinate. */
	static long floorOf(SplitDecimal p) { return p.getIntegerPart() + (long) Math.floor(p.getFractionalPart()); }

	/** p - floor(p), always in [0, 1). */
	static double fracOf(SplitDecimal p) {
		double f = p.getFractionalPart(), r = f - Math.floor(f);
		return r >= 1.0 ? Math.nextDown(1.0) : r;
	}

	/** floor(p + off) for a small offset (collision probes etc). */
	static long blockAt(SplitDecimal p, double off) {
		return p.getIntegerPart() + (long) Math.floor(p.getFractionalPart() + off);
	}

	static long chunkOf(SplitDecimal p) { return floorOf(p) >> SHIFT; }

	/** p += d (main thread only). */
	static void shift(SplitDecimal p, double d) {
		if (d != 0) { TMP.setValue(d); p.add(TMP, p); }
	}

	/** a - b as a double: exact for nearby values, saturates (never wraps) for huge gaps. Main thread only. */
	static double diff(SplitDecimal a, SplitDecimal b) {
		long ai = a.getIntegerPart(), bi = b.getIntegerPart(), d = ai - bi;
		if (((ai ^ bi) & (ai ^ d)) < 0) return (double) ai - (double) bi;
		a.subtract(b, TMP);
		return TMP.toDouble();
	}

	static SplitDecimal copyOf(SplitDecimal p) { SplitDecimal c = new SplitDecimal(); c.set(p); return c; }

	/** Exact decimal text -> split position ("123456789012345678.25", "1e18", ...). */
	static SplitDecimal parseCoord(String text) {
		java.math.BigDecimal v = new java.math.BigDecimal(text.trim());
		if (v.precision() - v.scale() > 19) throw new NumberFormatException("coordinate must be below 2^63");
		java.math.BigDecimal whole = v.setScale(0, java.math.RoundingMode.DOWN);
		long i;
		try { i = whole.longValueExact(); }
		catch (ArithmeticException e) { throw new NumberFormatException("coordinate must be below 2^63"); }
		return new SplitDecimal(i, v.subtract(whole).doubleValue());
	}

	static String coordStr(SplitDecimal p, boolean negate) {
		SplitDecimal c = new SplitDecimal();
		if (negate) p.negate(c); else c.set(p);
		return c.toString();
	}

	private static byte[] denseBuf() {
		byte[] b = GEN_DENSE.get();
		Arrays.fill(b, (byte) 0);
		return b;
	}

	/** Handles typing into the fog R/G/B/Hex boxes. Returns true if an edit was active (the key is consumed). */
	private boolean handleRgbEditKey(int code) {
		if (rgbEditChannel == -1) return false;
		if (code == KeyEvent.VK_ENTER) applyRgbEdit();
		else if (code == KeyEvent.VK_ESCAPE) { rgbEditChannel = -1; rgbEdit = ""; }
		else if (code == KeyEvent.VK_BACK_SPACE) { if (!rgbEdit.isEmpty()) rgbEdit = rgbEdit.substring(0, rgbEdit.length() - 1); }
		else if (rgbEditChannel == -2) { // hex
			char ch = 0;
			if (code >= KeyEvent.VK_0 && code <= KeyEvent.VK_9) ch = (char) code;
			else if (code >= KeyEvent.VK_NUMPAD0 && code <= KeyEvent.VK_NUMPAD9) ch = (char) ('0' + code - KeyEvent.VK_NUMPAD0);
			else if (code >= KeyEvent.VK_A && code <= KeyEvent.VK_F) ch = (char) code;
			if (ch != 0 && rgbEdit.length() < 6) rgbEdit += ch;
		} else { // 0..1 decimal
			char ch = 0;
			if (code >= KeyEvent.VK_0 && code <= KeyEvent.VK_9) ch = (char) ('0' + code - KeyEvent.VK_0);
			else if (code >= KeyEvent.VK_NUMPAD0 && code <= KeyEvent.VK_NUMPAD9) ch = (char) ('0' + code - KeyEvent.VK_NUMPAD0);
			else if (code == KeyEvent.VK_PERIOD || code == KeyEvent.VK_DECIMAL) ch = '.';
			if (ch != 0 && rgbEdit.length() < 5) rgbEdit += ch;
		}
		repaint();
		return true;
	}

	@Override
	public void keyPressed(KeyEvent e) {
		activity = System.currentTimeMillis();
		int code = e.getKeyCode();
		if (code == KeyEvent.VK_F11) { toggleFullscreenRequested = true; return; }
		if (mainMenu) { handleFrontKey(e); repaint(); return; }
		if (dead) { if (code == KeyEvent.VK_F2) takeScreenshot(); return; }
		if (!survival && !paused && !dialogOpen && code == KeyEvent.VK_F10) { paused=true; settingsMenu=false; lock=false; frame.setCursor(Cursor.getDefaultCursor()); openModifyDialog(); return; }
		if (modifyUi) {
            if(code==KeyEvent.VK_ESCAPE){modifyUi=false;dialogOpen=false;repaint();return;}
            String value=modifyValues[modifyFocus]==null?"":modifyValues[modifyFocus];
            boolean ctrl=e.isControlDown() || e.isMetaDown();
            if(ctrl && code==KeyEvent.VK_A){modifyAnchor=0;modifyCaret=value.length();repaint();return;}
            if(ctrl && (code==KeyEvent.VK_C || code==KeyEvent.VK_X)){
                int a=Math.min(modifyCaret,modifyAnchor), b=Math.max(modifyCaret,modifyAnchor);
                if(a!=b){try{Toolkit.getDefaultToolkit().getSystemClipboard().setContents(new StringSelection(value.substring(a,b)),null);}catch(Exception ignored){} }
                if(code==KeyEvent.VK_X && a!=b){modifyValues[modifyFocus]=value.substring(0,a)+value.substring(b);modifyCaret=modifyAnchor=a;}
                repaint();return;
            }
            if(ctrl && code==KeyEvent.VK_V){
                try{Object data=Toolkit.getDefaultToolkit().getSystemClipboard().getData(DataFlavor.stringFlavor); if(data instanceof String){String clip=(String)data; int a=Math.min(modifyCaret,modifyAnchor),b=Math.max(modifyCaret,modifyAnchor); modifyValues[modifyFocus]=value.substring(0,a)+clip+value.substring(b);modifyCaret=modifyAnchor=a+clip.length();}}catch(Exception ignored){} repaint();return;
            }
            if(code==KeyEvent.VK_TAB || code==KeyEvent.VK_ENTER){modifyFocus=(modifyFocus+1)%modifyValues.length; modifyCaret=modifyAnchor=(modifyValues[modifyFocus]==null?0:modifyValues[modifyFocus].length()); repaint();return;}
            if(code==KeyEvent.VK_LEFT){
                if(ctrl){int pos=Math.max(0,modifyCaret-1);while(pos>0&&Character.isWhitespace(value.charAt(pos)))pos--;while(pos>0&&!Character.isWhitespace(value.charAt(pos-1)))pos--;modifyCaret=pos;}
                else if(e.isShiftDown())modifyCaret=Math.max(0,modifyCaret-1);else if(modifyCaret!=modifyAnchor)modifyCaret=Math.min(modifyCaret,modifyAnchor);else modifyCaret=Math.max(0,modifyCaret-1);
                if(!e.isShiftDown())modifyAnchor=modifyCaret;repaint();return;
            }
            if(code==KeyEvent.VK_RIGHT){
                if(ctrl){int pos=Math.min(value.length(),modifyCaret);while(pos<value.length()&&!Character.isWhitespace(value.charAt(pos)))pos++;while(pos<value.length()&&Character.isWhitespace(value.charAt(pos)))pos++;modifyCaret=pos;}
                else if(e.isShiftDown())modifyCaret=Math.min(value.length(),modifyCaret+1);else if(modifyCaret!=modifyAnchor)modifyCaret=Math.max(modifyCaret,modifyAnchor);else modifyCaret=Math.min(value.length(),modifyCaret+1);
                if(!e.isShiftDown())modifyAnchor=modifyCaret;repaint();return;
            }
            if(code==KeyEvent.VK_HOME){modifyCaret=0;if(!e.isShiftDown())modifyAnchor=modifyCaret;repaint();return;}
            if(code==KeyEvent.VK_END){modifyCaret=value.length();if(!e.isShiftDown())modifyAnchor=modifyCaret;repaint();return;}
            if(code==KeyEvent.VK_BACK_SPACE || code==KeyEvent.VK_DELETE){
                int a=Math.min(modifyCaret,modifyAnchor),b=Math.max(modifyCaret,modifyAnchor);
                if(a!=b){modifyValues[modifyFocus]=value.substring(0,a)+value.substring(b);modifyCaret=modifyAnchor=a;}
                else if(code==KeyEvent.VK_BACK_SPACE&&modifyCaret>0){int from=modifyCaret-1;if(ctrl){while(from>0&&Character.isWhitespace(value.charAt(from)))from--;while(from>0&&!Character.isWhitespace(value.charAt(from-1)))from--;}modifyValues[modifyFocus]=value.substring(0,from)+value.substring(modifyCaret);modifyCaret=modifyAnchor=from;}
                else if(code==KeyEvent.VK_DELETE&&modifyCaret<value.length()){int to=modifyCaret+1;if(ctrl){while(to<value.length()&&!Character.isWhitespace(value.charAt(to)))to++;while(to<value.length()&&Character.isWhitespace(value.charAt(to)))to++;}modifyValues[modifyFocus]=value.substring(0,modifyCaret)+value.substring(to);modifyAnchor=modifyCaret;}
                repaint();return;
            }
            return;
        }

		if (paused) {
			if (handleRgbEditKey(code)) return;
			if (code == KeyEvent.VK_ESCAPE) { if(settingsMenu)settingsMenu=false; else if(quitConfirm)quitConfirm=false; else { paused=false; lock=true; mouseLookArmed=false; frame.setCursor(hidden); center(); } repaint(); return; }
			return;
		}
		if (code == KeyEvent.VK_ESCAPE) { paused=true; settingsMenu=false; quitConfirm=false; lock=false; frame.setCursor(Cursor.getDefaultCursor()); synchronized(input){input.clear();} velX=velY=velZ=0; repaint(); return; }
		if (code == KeyEvent.VK_F2) { takeScreenshot(); return; }
		if (code == KeyEvent.VK_CONTROL)
			sprintRequest = true;
		switch (code) {
		case KeyEvent.VK_P:
			if (detail < 3) {
				detail++;
				update = true;
			}
			break;
		case KeyEvent.VK_M:
			if (detail > -1) {
				detail--;
				update = true;
			}
			break;
		case KeyEvent.VK_F11:
			toggleFullscreenRequested = true;
			break;
		default:
			if (code >= 0 && code < 1024)
				synchronized (input) {
					input.set(code);
				}
			break;
		}
	}

	@Override
	public void keyReleased(KeyEvent e) {
		synchronized (input) {
			input.clear(e.getKeyCode());
		}
	}

	private void mouse(MouseEvent e) {
	    if (mainMenu || paused || dialogOpen || dead || toggleFullscreenRequested)
	        return;
	    // The first event after entering/resuming a world only recenters the cursor;
	    // do not interpret its old screen position as a look delta.
	    if (!mouseLookArmed) {
	        center();
	        mouseLookArmed = true;
	        return;
	    }

	    Point mousePos = MouseInfo.getPointerInfo().getLocation();
	    Point framePos = frame.getLocationOnScreen();
	    int centerX = framePos.x + frame.getWidth() / 2;
	    int centerY = framePos.y + frame.getHeight() / 2;
	    yaw += (mousePos.x - centerX) * sensitivity;
	    pitch -= (mousePos.y - centerY) * sensitivity;
	    center();
	}

	@Override
	public void mousePressed(MouseEvent e) {
		activity = System.currentTimeMillis();
		mouseButtonsDown++;
		if (mainMenu) {
            Point fp=SwingUtilities.convertPoint((Component)e.getSource(),e.getPoint(),this);
            if(frontScreen==3){double ms=menuUiScale();int ux=(int)Math.round(width/2.0+(fp.x-width/2.0)/ms), uy=(int)Math.round(height/2.0+(fp.y-height/2.0)/ms);int x0=Math.max(24,width/2-210), w=Math.min(420,width-48), y0=settingsY0(), halfW=(w-10)/2;menuSliderTarget=-1;
                if(settingsPage==0){if(uy>=y0+18&&uy<=y0+42)menuSliderTarget=2;else if(uy>=y0+66&&uy<=y0+90)menuSliderTarget=ux<x0+halfW?3:4;}
                else if(settingsPage==1){if(uy>=y0+18&&uy<=y0+42)menuSliderTarget=0;else if(uy>=y0+70&&uy<=y0+94)menuSliderTarget=1;else if(uy>=y0+110&&uy<=y0+134)menuSliderTarget=6;else if(uy>=y0+166&&uy<=y0+190)menuSliderTarget=5;else if(uy>=y0+336&&uy<=y0+360)menuSliderTarget=8;else if(!survival&&uy>=y0+386&&uy<=y0+410)menuSliderTarget=7;}
                menuSliderDragging=menuSliderTarget>=0;
            }
            if(frontScreen==2){menuSliderDragging=menuSliderTarget>=0;}
            frontMenuClick(fp.x,fp.y); return;
        }
		if (dead) { Point dp = SwingUtilities.convertPoint((Component) e.getSource(), e.getPoint(), this); deathClick(dp.x, dp.y); return; }
		if (modifyUi) { Point p=SwingUtilities.convertPoint((Component)e.getSource(),e.getPoint(),this); double gs=Math.max(1,scale); int mx=(int)Math.round(width/2.0+(p.x-width/2.0)/gs), my=(int)Math.round(height/2.0+(p.y-height/2.0)/gs); modifyUiClick(mx,my); return; }
		if (dialogOpen) return;
		if (paused) {
			Point p = SwingUtilities.convertPoint((Component) e.getSource(), e.getPoint(), this);
            int mx = p.x, my = p.y;
            double gs = Math.max(1, scale);
            mx = (int) Math.round(width / 2.0 + (mx - width / 2.0) / gs);
            my = (int) Math.round(height / 2.0 + (my - height / 2.0) / gs);
            int y0 = settingsY0();
            menuSliderTarget = -1;
            if (settingsMenu) {
                int x0=Math.max(24,width/2-210), w=Math.min(420,width-48);
                if(settingsPage==1) {
                    if(my>=y0+18&&my<=y0+42) menuSliderTarget=0;
                    else if(my>=y0+70&&my<=y0+94) menuSliderTarget=1;
                    else if(my>=y0+110&&my<=y0+134) menuSliderTarget=6;
                    else if(my>=y0+166&&my<=y0+190) menuSliderTarget=5;
                    else if(my>=y0+336&&my<=y0+360)menuSliderTarget=8;
                    else if(!survival&&my>=y0+386&&my<=y0+410)menuSliderTarget=7;
                } else {
                    if(my>=y0+18&&my<=y0+42) menuSliderTarget=2;
                    else if(my>=y0+66&&my<=y0+90) menuSliderTarget=mx<x0+(w-10)/2?3:4;
                }
            }
            menuSliderDragging = menuSliderTarget >= 0;
			menuClick(p.x, p.y);
			return;
		}
		final int b = e.getButton();
		if (b == 1) leftDown = true;
		if (b == 1 || b == 3)
			tasks.add(() -> click(b));
		else if (b == 2)
			tasks.add(Nexus::pick);
	}

	@Override
	public void mouseReleased(MouseEvent e) { mouseButtonsDown = Math.max(0, mouseButtonsDown - 1); if (e.getButton() == 1) leftDown = false; menuSliderDragging = false; menuSliderTarget = -1; }

	@Override
	public void mouseEntered(MouseEvent e) {
		if (!paused && !dead) center();
		inside = true;
		if (frame.isFocused() && !lock)
			mouse(e);
	}

	@Override
	public void mouseExited(MouseEvent e) {
		inside = false;
	}

	public void mouseClicked(MouseEvent e) {}

	@Override
	public void mouseDragged(MouseEvent e) {
		if (dialogOpen) return;
        if(mainMenu){if(frontScreen==3&&menuSliderDragging){Point p=SwingUtilities.convertPoint((Component)e.getSource(),e.getPoint(),this);menuSliderDrag(p.x,p.y);}return;}
		if (paused) {
            if (menuSliderDragging) {
                Point p = SwingUtilities.convertPoint((Component)e.getSource(), e.getPoint(), this);
                menuSliderDrag(p.x, p.y);
            }
			return;
		}
		if (inside && frame.isFocused() && !lock)
			mouse(e);
	}

	@Override
	public void mouseMoved(MouseEvent e) {
		activity = System.currentTimeMillis();
		if (inside && frame.isFocused() && !lock)
			mouse(e);
	}

	@Override
	public void focusGained(FocusEvent e) {
		activity = focusTime = System.currentTimeMillis();
		focus = true;
		if (mainMenu && frame != null) frame.setCursor(Cursor.getDefaultCursor());
	}

	@Override
	public void focusLost(FocusEvent e) {
		leftDown = false;
		mouseButtonsDown = 0;
		lock = !mainMenu;
		focus = false;
		synchronized (input) {
			input.clear(); // avoid stuck keys after alt-tab
		}
	}

	@Override
	public void mouseWheelMoved(MouseWheelEvent e) {
		if (mainMenu && frontScreen == 1) {
			int gui=frontGuiScale(), listH=Math.min(238*gui,Math.max(82*gui,height/4+10*gui));
			int visible=Math.max(1,(listH-12*gui)/(36*gui));
			int count=discoverSharedWorlds().size();
			worldScroll=Math.max(0,Math.min(Math.max(0,count-visible),worldScroll+Integer.signum(e.getWheelRotation())*Math.max(1,Math.abs(e.getWheelRotation()))));
			repaint(); return;
		}
		if (dead) return;
		int len = hotbar.length;
		int h = heldBlock + (e.getUnitsToScroll() < 0 ? -1 : 1);
		if (h < 0) h = len - 1;
		if (h >= len) h = 0;
		heldBlock = (byte) h;
	}

	public void keyTyped(KeyEvent e) {
        if (!modifyUi) return;
        char ch=e.getKeyChar();
        if (Character.isISOControl(ch)) return;
        if (!(Character.isDigit(ch) || ch=='-' || ch=='+' || ch=='.' || ch=='e' || ch=='E')) return;
        String value=modifyValues[modifyFocus]==null?"":modifyValues[modifyFocus];
        int a=Math.min(modifyCaret,modifyAnchor), b=Math.max(modifyCaret,modifyAnchor);
        modifyValues[modifyFocus]=value.substring(0,a)+ch+value.substring(b);
        modifyCaret=modifyAnchor=a+1;
        repaint();
    }
}

final class World {
	static final Octree UNLOADED = new Octree(0);
	static final long NONE = Long.MIN_VALUE;
	int w;
	long[] keys;
	Octree[] data;
	boolean[] dirty, user;
	long[] seen;
	int epoch;

	World(int radius) { resize(radius); }

	void resize(int radius) {
		final long[] oldKeys = keys;
		final Octree[] oldData = data;
		final boolean[] oldDirty = dirty, oldUser = user;
		final long[] oldSeen = seen;

		w = 2 * radius + 1;
		int n = w * w * w;
		keys = new long[n];
		data = new Octree[n];
		dirty = new boolean[n];
		user = new boolean[n];
		seen = new long[n];
		Arrays.fill(keys, NONE);

		// Re-seat every surviving chunk under the new ring size. Colliding chunks are dropped;
		// player edits were already stashed by flushDirty() before this is called, and
		// out-of-range chunks get unloaded by cleanupOldChunks().
		if (oldKeys != null) {
			for (int i = 0; i < oldKeys.length; i++) {
				if (oldKeys[i] == NONE) continue;
				long[] c = decodeKey(oldKeys[i]);
				int s = slot(c[0], c[1], c[2]);
				if (keys[s] != NONE) continue;
				keys[s] = oldKeys[i];
				data[s] = oldData[i];
				dirty[s] = oldDirty[i];
				user[s] = oldUser[i];
				seen[s] = oldSeen[i];
			}
		}
		worldVer++;
		streamVer++;
	}

	void clear() {
		epoch++;
		Arrays.fill(keys, NONE);
		Arrays.fill(data, null);
		Arrays.fill(dirty, false);
		Arrays.fill(user, false);
		worldVer++;
	}

	static long key(long cx, long cy, long cz) {
		return (cx & 0x1FFFFF) << 42 | (cy & 0x1FFFFF) << 21 | (cz & 0x1FFFFF);
	}

	static long[] decodeKey(long key) {
		long cx = (key >>> 42) & 0x1FFFFF, cy = (key >>> 21) & 0x1FFFFF, cz = key & 0x1FFFFF;
		if ((cx & 0x100000) != 0) cx |= ~0x1FFFFFL;
		if ((cy & 0x100000) != 0) cy |= ~0x1FFFFFL;
		if ((cz & 0x100000) != 0) cz |= ~0x1FFFFFL;
		return new long[] { cx, cy, cz };
	}

	static long unpackX(long k) { return (k << 1) >> 43; }
	static long unpackY(long k) { return (k << 22) >> 43; }
	static long unpackZ(long k) { return (k << 43) >> 43; }

	int slot(long cx, long cy, long cz) {
		int ix = (int) cx % w, iy = (int) cy % w, iz = (int) cz % w;
		if (ix < 0) ix += w;
		if (iy < 0) iy += w;
		if (iz < 0) iz += w;
		return (ix * w + iy) * w + iz;
	}

	boolean has(long cx, long cy, long cz) { return keys[slot(cx, cy, cz)] == key(cx, cy, cz); }

	Octree chunk(long cx, long cy, long cz) {
		int s = slot(cx, cy, cz);
		return keys[s] == key(cx, cy, cz) ? data[s] : UNLOADED;
	}

	void put(long cx, long cy, long cz, Octree d) {
		int s = slot(cx, cy, cz);
		data[s] = d;
		dirty[s] = false;
		user[s] = false;
		keys[s] = key(cx, cy, cz);
		seen[s] = System.currentTimeMillis();
		streamVer++;
	}

	void remove(long cx, long cy, long cz) {
		int s = slot(cx, cy, cz);
		if (keys[s] == key(cx, cy, cz)) {
			keys[s] = NONE;
			data[s] = null;
			dirty[s] = false;
			user[s] = false;
		}
		streamVer++;
	}
}

final class Render implements Callable<Void> {
	static int[] out;
	static int w, h;
	static double[] colX = new double[0], rowY = new double[0];
	static float[] invLen = new float[0];
	static double maxDist, px, py, pz, lx, ly, lz, rpx, rpy, rpz;
	static long pbx, pby, pbz;
	static double cachedFocal = Double.NaN;
	static int cachedW, cachedH;
	static double sunR, sunG, sunB, ambR, ambG, ambB, skyR, skyG, skyB;
	static boolean cls, hl;
	static long hvX, hvY, hvZ;
	static final AtomicInteger next = new AtomicInteger();
	static final double INF = Double.POSITIVE_INFINITY, EPS = 1e-4;
	static float[] depth = new float[0];
	static double xScale, yScale, shadowDist;
	static int cachedWinW, cachedWinH;
	static final int SHADOW_RANGE = 128;
	static boolean[] opaque = new boolean[256];
	private int seenWorld = -1, seenStream = -1;
    private int shadowCacheWorld = -1;
	Semaphore go;
	static final byte TILE = 16;
	static int tilesX, tilesTotal, fogStamp;
	static int[] tileOrder = new int[0];
	static long ceilY;
	static double marchDist;
	private long fqx = Long.MIN_VALUE, fqy, fqz;
	private int fogSeen = -1;
	static double slx, sly, slz;
	static int sunVer;
	static long sunTick = Long.MIN_VALUE;
	/** Minimum skylight / ambient base once fully underground (surface values are 0.78 and 0.18). Lower = darker caves. */
	static final double CAVE_SKY_MIN = 0.035, CAVE_AMB_BASE = 0.045;
	static final double DEEP_SHADOW = 384;   // shadow ray length for faces that are under cover
	static final int SKY_RAY = 256;          // sky-light ray length (was 64)
	private boolean hUnloaded;               // set by march(): the ray ended in an unloaded chunk
	private boolean shadowUnloaded;          // provisional shadow result crossed an unloaded chunk
	private boolean skyUnloaded;             // one or more sky samples crossed an unloaded chunk
	private double skyOpen = 1;              // fraction of sky rays that escaped (set by skyLight)
	private int seenLight = -1;
	private boolean lightProvisional;   // this block-light result used an unloaded chunk: don't cache it
	private double blR, blG, blB;
	/** How far (blocks) emitted light reaches, and how strong it is. */
	static final int LIGHT_R = 15;
	static final double BLOCK_LIGHT_GAIN = 0.6;     // the sphere is larger, so this is lowered to keep walls from clipping
	static final double LIGHT_NEAR = 64, LIGHT_FAR = 128; // exact nearby, then 2-block / 4-block cached light cells
	/** Hard ceiling on the emitted-light contribution per colour channel (the old code allowed 2.0). */
	static final double BLOCK_LIGHT_MAX = 1.0;
	static volatile boolean warmIncomplete;
	static long warmDeadline = Long.MAX_VALUE;
	static final long WARM_BUDGET_NS = 1_000_000_000L;
	private boolean fast;
	/** Light colour per emitter (default white). */
	static final double[][] GLOW_TINT = new double[BLOCK_COUNT][];
	private static final int LCACHE = 1 << 14;
	private final long[] lKey = new long[LCACHE];
	private final int[] lVal = new int[LCACHE];
	// Falloff tables, built once. ISQ[v] = floor(sqrt(v)); PRE holds a smooth cubic falloff
	// integrated along x, so a run of voxels is one subtraction without a hard-edged light cutoff.
	static final int[] ISQ = new int[LIGHT_R * LIGHT_R + 1];
	static final double[] PRE;
	static {
		for (byte i = 0; i < BLOCK_COUNT; i++) GLOW_TINT[i] = new double[] { 1, 1, 1 };
		GLOW_TINT[MAGMA]     = new double[] { 1.0, 0.50, 0.12 };
		GLOW_TINT[RUBY]      = new double[] { 1.0, 0.20, 0.30 };
		GLOW_TINT[AMETHYST]  = new double[] { 0.70, 0.30, 1.0 };
		GLOW_TINT[SAPPHIRE]  = new double[] { 0.30, 0.50, 1.0 };
		GLOW_TINT[TOPAZ]     = new double[] { 1.0, 0.85, 0.30 };
		GLOW_TINT[DIAMOND]   = new double[] { 0.60, 0.90, 1.0 };
		GLOW_TINT[EMERALD]   = new double[] { 0.30, 1.0, 0.40 };
		GLOW_TINT[TANZANITE] = new double[] { 0.0,  0.0,  1.0 };
		GLOW_TINT[RHODONITE] = new double[] { 1.0,  0.0,  1.0 };
		GLOW_TINT[DYNAMITE]  = new double[] { 1.0,  0.0,  0.0 };
		final int R = LIGHT_R, W = 2 * R + 2;
		for (int v = 0; v < ISQ.length; v++) ISQ[v] = (int) Math.sqrt(v);
		PRE = new double[R * R * W];
		for (int rowSq = 0; rowSq < R * R; rowSq++) {
			int b = rowSq * W;
			for (int j = 0; j <= 2 * R; j++) {
				int dx = j - R;
				double d = Math.sqrt(rowSq + (double) dx * dx);
				double t = d / R;
				double w = t < 1.0 ? (1.0 - t * t * (3.0 - 2.0 * t)) : 0.0;
				PRE[b + j + 1] = PRE[b + j] + w;
			}
		}
	}

	private static int tileOrderX = -1, tileOrderY = -1;

	static void buildTileOrder(int tilesY) {
	    if (tileOrder.length == tilesTotal && tileOrderX == tilesX && tileOrderY == tilesY) return;
	    if (tileOrder.length != tilesTotal) tileOrder = new int[tilesTotal];
	    int centreX = tilesX / 2, centreY = tilesY / 2, written = 0;
	    int maxRing = Math.max(tilesX, tilesY);
	    for (int ring = 0; ring < maxRing && written < tilesTotal; ring++) {
	        int minX = centreX - ring, maxX = centreX + ring, minY = centreY - ring, maxY = centreY + ring;
	        for (int tx = minX; tx <= maxX; tx++) {
	            if (minY >= 0 && minY < tilesY && tx >= 0 && tx < tilesX) tileOrder[written++] = minY * tilesX + tx;
	            if (maxY != minY && maxY >= 0 && maxY < tilesY && tx >= 0 && tx < tilesX) tileOrder[written++] = maxY * tilesX + tx;
	        }
	        for (int ty = minY + 1; ty < maxY; ty++) {
	            if (ty < 0 || ty >= tilesY) continue;
	            if (minX >= 0 && minX < tilesX) tileOrder[written++] = ty * tilesX + minX;
	            if (maxX != minX && maxX >= 0 && maxX < tilesX) tileOrder[written++] = ty * tilesX + maxX;
	        }
	    }
	    tileOrderX = tilesX; tileOrderY = tilesY;
	}

	static void prepare() {
		out = buffer;
		w = resX;
		h = resY;
		final int ww = width, wh = height;
		if (colX.length != w) colX = new double[w];
		if (rowY.length != h) rowY = new double[h];
		if (invLen.length != w * h) invLen = new float[w * h];
		if (depth.length != w * h) depth = new float[w * h];
		double invFocal = 1.0 / focal;
		xScale = invFocal * ww / (4.0 * w);
		yScale = invFocal * wh / (4.0 * h);
		if (cachedW != w || cachedH != h || cachedFocal != focal || cachedWinW != ww || cachedWinH != wh) {
			double xOrigin = w * 0.5, yOrigin = h * 0.5;
			for (int i = 0; i < w; i++)
				colX[i] = (i - xOrigin) * xScale;
			for (int j = 0; j < h; j++)
				rowY[j] = (j - yOrigin) * yScale;
			for (int row = 0; row < h; row++) {
				double fy = rowY[row];
				int base = row * w;
				for (int col = 0; col < w; col++) {
					double fx = colX[col];
					invLen[base + col] = (float) (1.0 / Math.sqrt(fx * fx + fy * fy + 1.0));
				}
			}
			cachedW = w;
			cachedH = h;
			cachedFocal = focal;
			cachedWinW = ww;
			cachedWinH = wh;
		}
		shadowDist = Math.min(dist, SHADOW_RANGE);
		maxDist = dist;
		marchDist = maxDist / (1.0 + 0.6 * Nexus.caveMix);  // fog is opaque by then (min density 1.0 outside, 1.6 in caves)
		ceilY = Math.min(Nexus.topBound(), Nexus.userTopY); // nothing exists above this row
		cls = classic;
		opaque = Nexus.OPAQUE;
		hl = display;
		hvX = hoveredX;
		hvY = hoveredY;
		hvZ = hoveredZ;
		pbx = Nexus.floorOf(Nexus.viewX);
		pby = Nexus.floorOf(Nexus.viewY);
		pbz = Nexus.floorOf(Nexus.viewZ);
		rpx = Nexus.fracOf(Nexus.viewX);
		rpy = Nexus.fracOf(Nexus.viewY);
		rpz = Nexus.fracOf(Nexus.viewZ);
		lx = light.x;
		ly = light.y;
		lz = light.z;
		long tk = Nexus.time;
		if (SHADOW_REFRESH_TICKS <= 0 || sunTick == Long.MIN_VALUE || tk < sunTick || tk - sunTick >= SHADOW_REFRESH_TICKS) {
			sunTick = tk;
			slx = lx; sly = ly; slz = lz;
			sunVer++;
		}
		sunR = sunColor.x; sunG = sunColor.y; sunB = sunColor.z;
		ambR = ambColor.x; ambG = ambColor.y; ambB = ambColor.z;
		skyR = skyColor.x; skyG = skyColor.y; skyB = skyColor.z;
		prepareFog();
		tilesX = (w + TILE - 1) / TILE;
		tilesTotal = tilesX * ((h + TILE - 1) / TILE);
		buildTileOrder((h + TILE - 1) / TILE);
		warmIncomplete = false;
		warmDeadline = Nexus.lightWarming() ? System.nanoTime() + WARM_BUDGET_NS : Long.MAX_VALUE;
		next.set(0);
	}

	private long ccx, ccy, ccz;
	private Octree cchunk;
	// leaf cache: an aligned cube (uniform id, or a packed 2x2x2 cell whose 8 bytes are in cval)
	private long cox, coy, coz, csz, cval;
	private int cinfo;
	private boolean cpk;
	// last hit
	private double hT, hHx, hHy, hHz, hR, hG, hB;
	private byte hAxis, hSign, hId;
	static double cave, fLR = 1, fLG = 1, fLB = 1, fogCamR, fogCamG, fogCamB;
	static final Fog camFog = new Fog();
	private final Fog fog = new Fog();
	private long hBx, hBy, hBz;

	@Override
	public Void call() {
		if (seenLight != Nexus.lightVer || seenWorld != Nexus.worldVer|| seenStream != Nexus.streamVer) {
	        Arrays.fill(lKey, 0L);
	        seenLight = Nexus.lightVer;
	        seenWorld = Nexus.worldVer;
	        seenStream = Nexus.streamVer;
	    }
	    if (shadowCacheWorld != Nexus.worldVer) {
	        shMemo.requestClear();
	        shadowCacheWorld = Nexus.worldVer;
	    }
		ccx = ccy = ccz = Long.MIN_VALUE;
		cchunk = null;
		csz = 0;
		int tile;
		while ((tile = next.getAndIncrement()) < tilesTotal) {
			tile = tileOrder[tile];
			fast = Nexus.lightWarming() && System.nanoTime() < warmDeadline;
			if (fast) warmIncomplete = true;
			int c0 = (tile % tilesX) * TILE, r0 = (tile / tilesX) * TILE;
			int c1 = Math.min(w, c0 + TILE), r1 = Math.min(h, r0 + TILE);
            for (int row = r0; row < r1; row++)
                renderRow(row, c0, c1);
		}
		return null;
	}

	/** v + s, but stays at v instead of wrapping when it would overflow. */
	private static long sat(long v, int s) {
		long r = v + s;
		return ((v ^ r) & (s ^ r)) < 0 ? v : r;
	}

	private static long tex16(double v) {
		return ((long) Math.floor(v)) & 15;
	}

	/** Main thread only, call while workers are idle. */
	void beginParticleLight() { ccx = ccy = ccz = Long.MIN_VALUE; cchunk = null; csz = 0; }

	static final double PARTICLE_RAY_DIST = 64;

	int litParticle(int c, long bx, long by, long bz, double k) {
	    double sky = 1, open = 1 - cave;
	    if (lightQ >= 2 && k < PARTICLE_RAY_DIST) { sky = skyLight(bx, by, bz); open = skyOpen; }
	    double shade = Math.max(cave, 1 - smoothstep(0.0, 0.85, open));
	    sky = Math.max(0.78 + (CAVE_SKY_MIN - 0.78) * shade, sky);
	    double base = 0.18 + (CAVE_AMB_BASE - 0.18) * shade;
	    double amb = base + (1 - base) * sky, sun = 0.45 * open;
	    double lr = ambR * amb + sunR * sun, lg = ambG * amb + sunG * sun, lb = ambB * amb + sunB * sun;
	    if (Nexus.blockLightingEnabled && lightQ >= 1) { blockLight(bx, by, bz, k); lr += blR; lg += blG; lb += blB; }
	    int r = Math.min(255, (int) ((c >> 16 & 255) * lr));
	    int g = Math.min(255, (int) ((c >> 8 & 255) * lg));
	    int b = Math.min(255, (int) ((c & 255) * lb));
	    return r << 16 | g << 8 | b;
	}

	private static final int GLOW_NEAR_CACHE_SIZE = 1 << 14;
	private static final long[] glowNearTable = new long[GLOW_NEAR_CACHE_SIZE];

	private boolean glowNearby(long x, long y, long z) {
	    long bx = Math.floorDiv(x, 8), by = Math.floorDiv(y, 8), bz = Math.floorDiv(z, 8);
	    int version = 31 * worldVer + streamVer;
	    long key = Memo.hash(bx, by, bz, 7L ^ ((long) version << 8));
	    int slot = (int) (key >>> 20) & (GLOW_NEAR_CACHE_SIZE - 1);
	    long e = glowNearTable[slot];
	    if (((e ^ key) & ~0xFFL) == 0 && (e & 0xFF) != 0)
	        return (e & 0xFF) == 2;
	    final long x0 = (bx * 8 - LIGHT_R) >> SHIFT, x1 = (bx * 8 + 7 + LIGHT_R) >> SHIFT;
	    final long y0 = (by * 8 - LIGHT_R) >> SHIFT, y1 = (by * 8 + 7 + LIGHT_R) >> SHIFT;
	    final long z0 = (bz * 8 - LIGHT_R) >> SHIFT, z1 = (bz * 8 + 7 + LIGHT_R) >> SHIFT;
	    boolean found = false, sawUnloaded = false;
	    for (long cz = z0; cz <= z1 && !found; cz++)
	        for (long cy = y0; cy <= y1 && !found; cy++)
	            for (long cx = x0; cx <= x1; cx++) {
	                Octree c = world.chunk(cx, cy, cz);
	                if (c == World.UNLOADED) { sawUnloaded = true; continue; }
	                if (c != null && c.mayGlow(GLOW)) { found = true; break; }
	            }
	    if (!found && sawUnloaded) { lightProvisional = true; return false; }
	    glowNearTable[slot] = (key & ~0xFFL) | (found ? 2 : 1);
	    return found;
	}

	/** Sums light from emitters within LIGHT_R into blR/blG/blB. Exact per block nearby, 4-block cells far away. */
	private void blockLight(long fx, long fy, long fz, double t) {
		lightProvisional = false;
		final int s = t < LIGHT_NEAR ? 0 : t < LIGHT_FAR ? 1 : 2;
	    final long qx = fx >> s, qy = fy >> s, qz = fz >> s;
	    final long h = Memo.hash(qx, qy, qz, s);
	    final int slot = (int) (h >>> 20) & (LCACHE - 1);
	    if (lKey[slot] == h) {
	        int v = lVal[slot];
	        final double u = BLOCK_LIGHT_MAX / 1023.0;
	        blR = (v & 1023) * u; blG = ((v >> 10) & 1023) * u; blB = ((v >> 20) & 1023) * u;
	        return;
	    }
	    final int half = (1 << s) >> 1;
	    final long ox = (qx << s) + half, oy = (qy << s) + half, oz = (qz << s) + half;
	    if (!glowNearby(ox, oy, oz)) { // most of the world has no emitter within reach
	        blR = blG = blB = 0;
	        if (!lightProvisional) { lVal[slot] = 0; lKey[slot] = h; }
	        return;
	    }
	    final int R = LIGHT_R, W = 2 * R + 2, R2m = R * R - 1;
	    double sr = 0, sg = 0, sb = 0;
		byte emittersSeen = 0;
		// Dense clusters saturate visually. Stop tracing additional emitters once enough
		// nearby sources have been accumulated; this avoids thousands of redundant probes.
		lightScan: for (int dz = -R; dz <= R; dz++) {
			final int remZ = R2m - dz * dz;
			if (remZ < 0) continue;
			final int dyMax = ISQ[remZ];
			final long z = oz + dz;
			for (int dy = -dyMax; dy <= dyMax; dy++) {
				final int rowSq = dy * dy + dz * dz;
				final int lim = ISQ[R2m - rowSq];
				final int base = rowSq * W + R;
				final long y = oy + dy;
				int dx = -lim;
				while (dx <= lim) {
					final long x = ox + dx;
					final int info = probe(x, y, z);
				    if (info < 0) { // unloaded chunk: skip to the end of it
				    	lightProvisional = true;
				      	dx = (int) ((x | MASK) + 1 - ox);
				      	continue;
				    }
					final int id = info & 0xFF, lg = info >> 8;
					int end = dx; // last dx covered by this leaf cube
					if (lg > 0) {
						long cubeEnd = ((x & ~((1L << lg) - 1)) + (1L << lg) - 1) - ox;
						end = (int) Math.min(lim, cubeEnd);
					}
					if (id < GLOW.length && GLOW[id] > 0) {
						double w = (PRE[base + end + 1] - PRE[base + dx]) * GLOW[id] * BLOCK_LIGHT_GAIN;
						double[] tint = GLOW_TINT[id];
						sr += w * tint[0]; sg += w * tint[1]; sb += w * tint[2];
						if (++emittersSeen >= 48) break lightScan;
					}
					dx = end + 1;
				}
			}
		}

		// Clamp by scaling all channels together so the tint is preserved.
		double peak = Math.max(sr, Math.max(sg, sb));
		if (peak > BLOCK_LIGHT_MAX) {
			double k = BLOCK_LIGHT_MAX / peak;
			sr *= k; sg *= k; sb *= k;
		}
		blR = sr; blG = sg; blB = sb;
	    if (!lightProvisional) {
	    	final double inv = 1023.0 / BLOCK_LIGHT_MAX;
	    	lVal[slot] = (int) Math.round(sr * inv) | (int) Math.round(sg * inv) << 10 | (int) Math.round(sb * inv) << 20;
	    	lKey[slot] = h;
	    }
	}

	private int probe(long bx, long by, long bz) {
		if (csz > 0
		        && (bx & ~(csz - 1)) == cox
		        && (by & ~(csz - 1)) == coy
		        && (bz & ~(csz - 1)) == coz) {
		    return cpk ? (int) ((cval >>> ((int) ((bx & 1) | ((by & 1) << 1) | ((bz & 1) << 2)) << 3)) & 0xFF) : cinfo;
		}
		long cx = bx >> SHIFT, cy = by >> SHIFT, cz = bz >> SHIFT;
		if (cx != ccx || cy != ccy || cz != ccz) {
			ccx = cx; ccy = cy; ccz = cz;
			cchunk = world.chunk(cx, cy, cz);
		}
		Octree c = cchunk;
		if (c == World.UNLOADED)
			return -1;
		int info = c == null ? 6 << 8 : c.find((int) (bx & MASK), (int) (by & MASK), (int) (bz & MASK));
		if (info < 0) { // mixed 2x2x2 cell: remember all 8 voxels
			cval = c.cells[info & Octree.PMASK];
			cpk = true;
			csz = 2;
			cox = bx & ~1L; coy = by & ~1L; coz = bz & ~1L;
			return (int) ((cval >>> ((int) ((bx & 1) | ((by & 1) << 1) | ((bz & 1) << 2)) << 3)) & 0xFF);
		}
		cpk = false;
		long sz = 1L << (info >> 8), m = ~(sz - 1);
		cox = bx & m; coy = by & m; coz = bz & m;
		csz = sz;
		cinfo = info;
		return info;
	}

	private void renderRow(int row, int c0, int c1) {
		int base = row * w;
		double fy = rowY[row];
		double sp = sinPitch, cp = cosPitch, sy = sinYaw, cy = cosYaw;
		double temp = cp + fy * sp;
		double dyBase = fy * cp - sp;
		for (int col = c0; col < c1; col++) {
			double fx = colX[col];
			double inv = invLen[base + col];
			double dx = (fx * cy + temp * sy) * inv;
			double dy = dyBase * inv;
			double dz = (temp * cy - fx * sy) * inv;
			final int centerCol = w / 2;
			final int centerRow = h / 2;
			final boolean center = col == centerCol && row == centerRow;
			double r, g, b;
			depth[base + col] = Float.MAX_VALUE;
			if (march(rpx, rpy, rpz, dx, dy, dz, marchDist, true, center)) {
				depth[base + col] = (float) hT;
				if (cls) shadeClassic(); else shadeModern();
				r = hR; g = hG; b = hB;
			} else if (cls) {
				r = fogCamR; g = fogCamG; b = fogCamB;
			} else if (dx * lx + dy * ly + dz * lz > 0.99) {
				r = sunR; g = sunG; b = sunB;
			} else { // sky blends into the biome fog at the horizon (and into cave fog underground)
				double k = Math.max(cave, 0.85 * Math.max(0, 1 - Math.abs(dy) * 3));
				r = skyR + (fogCamR - skyR) * k;
				g = skyG + (fogCamG - skyG) * k;
				b = skyB + (fogCamB - skyB) * k;
			}
			int ri = (int) (r * 255.0);
			int gi = (int) (g * 255.0);
			int bi = (int) (b * 255.0);
			if (ri < 0) ri = 0; else if (ri > 255) ri = 255;
			if (gi < 0) gi = 0; else if (gi > 255) gi = 255;
			if (bi < 0) bi = 0; else if (bi > 255) bi = 255;
			int rgb = (ri << 16) | (gi << 8) | bi;
            out[base + col] = rgb;
		}
	}

	/** Number of voxel-boundary crossings on one axis that happen strictly before te (at most cap). */
	private static long crossed(double tm, double td, double te, long cap) {
		if (tm >= te)
			return 0;
		long k = (long) Math.floor((te - tm) / td) + 1;
		while (k > 0 && tm + (k - 1) * td >= te) k--; // fix rounding in both directions
		while (tm + k * td < te) k++;
		return Math.min(k, cap);
	}

	private boolean occluded(double ox, double oy, double oz, double dx, double dy, double dz, double maxT, boolean blockUnloaded) {
		if (dy < 0) {
			final double top = (double) (ceilY - pby);
			if (oy >= top) {
				double tUp = (oy - top) / -dy;
				if (tUp < maxT) maxT = tUp + 1e-6;
			}
		}
		long rx = (long) Math.floor(ox), ry = (long) Math.floor(oy), rz = (long) Math.floor(oz);
		long bx = pbx + rx, by = pby + ry, bz = pbz + rz;
		int sx = dx > 0 ? 1 : dx < 0 ? -1 : 0;
		int sy = dy > 0 ? 1 : dy < 0 ? -1 : 0;
		int sz = dz > 0 ? 1 : dz < 0 ? -1 : 0;
		double tdx = sx == 0 ? INF : 1.0 / Math.abs(dx);
		double tdy = sy == 0 ? INF : 1.0 / Math.abs(dy);
		double tdz = sz == 0 ? INF : 1.0 / Math.abs(dz);
		double tmx = sx == 0 ? INF : (sx > 0 ? (double) (rx + 1) - ox : ox - rx) * tdx;
		double tmy = sy == 0 ? INF : (sy > 0 ? (double) (ry + 1) - oy : oy - ry) * tdy;
		double tmz = sz == 0 ? INF : (sz > 0 ? (double) (rz + 1) - oz : oz - rz) * tdz;

		for (int steps = (int) (3 * maxT) + 16; steps-- > 0;) {
			int axis;
			double t;
			if (tmx < tmy) {
				if (tmx < tmz) { axis = 0; t = tmx; } else { axis = 2; t = tmz; }
			} else {
				if (tmy < tmz) { axis = 1; t = tmy; } else { axis = 2; t = tmz; }
			}
			if (t >= maxT)
				return false;
			switch (axis) {
			case 0: bx = sat(bx, sx); tmx += tdx; break;
			case 1: by = sat(by, sy); tmy += tdy; break;
			default: bz = sat(bz, sz); tmz += tdz; break;
			}
			int info;
			for (;;) {
				info = probe(bx, by, bz);
				if (info < 0) {
					shadowUnloaded = true;
					return blockUnloaded; // unloaded: shadow rays under cover treat it as solid
				}
				int lg = info >> 8;
				if ((info & 0xFF) != AIR || lg == 0)
					break;
				long S = 1L << lg, M = ~(S - 1);
				long x0c = bx & M, y0c = by & M, z0c = bz & M;
				long nx = sx > 0 ? x0c + S - bx : sx < 0 ? bx - x0c + 1 : 0;
				long ny = sy > 0 ? y0c + S - by : sy < 0 ? by - y0c + 1 : 0;
				long nz = sz > 0 ? z0c + S - bz : sz < 0 ? bz - z0c + 1 : 0;
				double ex = sx == 0 ? INF : tmx + (nx - 1) * tdx;
				double ey = sy == 0 ? INF : tmy + (ny - 1) * tdy;
				double ez = sz == 0 ? INF : tmz + (nz - 1) * tdz;
				int ea;
				double te;
				if (ex <= ey && ex <= ez) { ea = 0; te = ex; }
				else if (ey <= ez) { ea = 1; te = ey; }
				else { ea = 2; te = ez; }
				if (te >= maxT)
					return false;
				long kx = ea == 0 ? nx : (sx == 0 ? 0 : crossed(tmx, tdx, te, nx - 1));
				long ky = ea == 1 ? ny : (sy == 0 ? 0 : crossed(tmy, tdy, te, ny - 1));
				long kz = ea == 2 ? nz : (sz == 0 ? 0 : crossed(tmz, tdz, te, nz - 1));
				if (kx != 0) { bx += sx * kx; tmx += kx * tdx; }
				if (ky != 0) { by += sy * ky; tmy += ky * tdy; }
				if (kz != 0) { bz += sz * kz; tmz += kz * tdz; }
				axis = ea;
				t = te;
			}
			int id = info & 0xFF;
			if (id == AIR)
				continue;
			if (opaque[id])
				return true; // every texel solid: no hit position or texture lookup needed
			if (id == GLASS) {
				long ax = bx - (axis == 0 ? sx : 0), ay = by - (axis == 1 ? sy : 0), az = bz - (axis == 2 ? sz : 0);
				if (getBlock(ax, ay, az) == GLASS)
					continue;
			}
			// leaves / glass: same texel test as march()
			double hx = ox + dx * t, hy = oy + dy * t, hz = oz + dz * t;
			int texX, texY;
			if (axis == 1) {
				texX = (int) tex16(hx * 16);
				texY = (int) tex16(hz * 16);
				if (dy < 0.0)
					texY += 32;
			} else {
				texX = (int) tex16((hx + hz) * 16);
				texY = (int) tex16(hy * 16) + 16;
			}
			if ((atlas[texX + texY * 16 + id * 768] & 0xFFFFFF) != 0)
				return true;
		}
		return false;
	}

	/** Sub-cell index of (pb + h) at resolution G; wraps harmlessly past 2^59. */
	private static long cellIdx(long pb, double h, int G) {
		double f = Math.floor(h);
		return (pb + (long) f) * G + (long) Math.floor((h - f) * G);
	}

	/** Centre of sub-cell c, relative to the camera block pb. */
	private static double cellCentre(long c, long pb, int G) {
		return ((c - pb * G) + 0.5) / G;
	}

	private boolean inShadow(double hx, double hy, double hz, int axis, int sign, long fx, long fy, long fz, double t, boolean deep) {
		int G = SHADOW_GRID;
		double ox = hx, oy = hy, oz = hz;
		long key = 0;
		if (G > 0) {
			double fp = t * Math.max(xScale, yScale);
			while (G > 4 && G * fp * SHADOW_LOD > 1.0)
				G >>= 1;
			long cu, cv, nw;
			switch (axis) {
			case 0:
				cu = cellIdx(pby, hy, G); cv = cellIdx(pbz, hz, G); nw = fx;
				oy = cellCentre(cu, pby, G); oz = cellCentre(cv, pbz, G);
				break;
			case 1:
				cu = cellIdx(pbx, hx, G); cv = cellIdx(pbz, hz, G); nw = fy;
				ox = cellCentre(cu, pbx, G); oz = cellCentre(cv, pbz, G);
				break;
			default:
				cu = cellIdx(pbx, hx, G); cv = cellIdx(pby, hy, G); nw = fz;
				ox = cellCentre(cu, pbx, G); oy = cellCentre(cv, pby, G);
			}
			long epoch = ((long) Nexus.worldVer << 32) ^ (Nexus.streamVer & 0xFFFFFFFFL);
			key = Memo.hash(cu, cv, nw, (((long) sunVer) << 32) ^ epoch ^ (deep ? 512L : 0L) ^ ((long) G << 4) ^ (axis << 1) ^ (sign > 0 ? 1L : 0L));
			int c = shMemo.get(key);
			if (c >= 0)
				return c != 0;
		}
		double nx = axis == 0 ? sign : 0, ny = axis == 1 ? sign : 0, nz = axis == 2 ? sign : 0;
		shadowUnloaded = false;
		boolean s = occluded(ox + nx * EPS, oy + ny * EPS, oz + nz * EPS, slx, sly, slz, deep ? DEEP_SHADOW : shadowDist, deep);
		if (G > 0 && !shadowUnloaded)
			shMemo.put(key, s ? 1 : 0);
		return s;
	}

	private boolean march(double ox, double oy, double oz, double dx, double dy, double dz, double maxT, boolean primary, boolean center) {
		hUnloaded = false;
		final double tBase = 0;
		final double top = (double) (ceilY - pby);
		if (dy < 0 && oy >= top) {              // heading up from inside the terrain band: it can never hit anything past the ceiling
			double tUp = (oy - top) / -dy;
			if (tUp < maxT) maxT = tUp + 1e-6;
		}
		long rx = (long) Math.floor(ox), ry = (long) Math.floor(oy), rz = (long) Math.floor(oz);
		long bx = pbx + rx, by = pby + ry, bz = pbz + rz;
		int sx = dx > 0 ? 1 : dx < 0 ? -1 : 0;
		int sy = dy > 0 ? 1 : dy < 0 ? -1 : 0;
		int sz = dz > 0 ? 1 : dz < 0 ? -1 : 0;

		double tdx = sx == 0 ? INF : 1.0 / Math.abs(dx);
		double tdy = sy == 0 ? INF : 1.0 / Math.abs(dy);
		double tdz = sz == 0 ? INF : 1.0 / Math.abs(dz);
		double tmx = sx == 0 ? INF : (sx > 0 ? (double) (rx + 1) - ox : ox - rx) * tdx;
		double tmy = sy == 0 ? INF : (sy > 0 ? (double) (ry + 1) - oy : oy - ry) * tdy;
		double tmz = sz == 0 ? INF : (sz > 0 ? (double) (rz + 1) - oz : oz - rz) * tdz;
		boolean hoverPending = primary && center;

		for (int steps = (int) (3 * maxT) + 16; steps-- > 0;) {
			byte axis;
			double t;
			if (tmx < tmy) {
				if (tmx < tmz) { axis = 0; t = tmx; } else { axis = 2; t = tmz; }
			} else {
				if (tmy < tmz) { axis = 1; t = tmy; } else { axis = 2; t = tmz; }
			}
			if (t >= maxT)
				return false;
			switch (axis) {
			case 0: bx = sat(bx, sx); tmx += tdx; break;
			case 1: by = sat(by, sy); tmy += tdy; break;
			default: bz = sat(bz, sz); tmz += tdz; break;
			}
			int info;
			for (;;) {
				info = probe(bx, by, bz);
				if (info < 0) { hUnloaded = true; return false; }
				int lg = info >> 8;
				if ((info & 0xFF) != AIR || lg == 0)
					break;
				// Air cube of side 2^lg: jump to where the ray leaves it.
				long S = 1L << lg, M = ~(S - 1);
				long x0c = bx & M, y0c = by & M, z0c = bz & M;
				long nx = sx > 0 ? x0c + S - bx : sx < 0 ? bx - x0c + 1 : 0;
				long ny = sy > 0 ? y0c + S - by : sy < 0 ? by - y0c + 1 : 0;
				long nz = sz > 0 ? z0c + S - bz : sz < 0 ? bz - z0c + 1 : 0;
				double ex = sx == 0 ? INF : tmx + (nx - 1) * tdx;
				double ey = sy == 0 ? INF : tmy + (ny - 1) * tdy;
				double ez = sz == 0 ? INF : tmz + (nz - 1) * tdz;
				byte ea;
				double te;
				if (ex <= ey && ex <= ez) { ea = 0; te = ex; }
				else if (ey <= ez) { ea = 1; te = ey; }
				else { ea = 2; te = ez; }
				if (te >= maxT)
					return false;
				long kx = ea == 0 ? nx : (sx == 0 ? 0 : crossed(tmx, tdx, te, nx - 1));
				long ky = ea == 1 ? ny : (sy == 0 ? 0 : crossed(tmy, tdy, te, ny - 1));
				long kz = ea == 2 ? nz : (sz == 0 ? 0 : crossed(tmz, tdz, te, nz - 1));
				if (kx != 0) { bx += sx * kx; tmx += kx * tdx; }
				if (ky != 0) { by += sy * ky; tmy += ky * tdy; }
				if (kz != 0) { bz += sz * kz; tmz += kz * tdz; }
				axis = ea;
				t = te;
			}
			byte id = (byte) (info & 0xFF);
			if (id == AIR)
				continue;

			if (id == GLASS) {
				long ax = bx - (axis == 0 ? sx : 0);
				long ay = by - (axis == 1 ? sy : 0);
				long az = bz - (axis == 2 ? sz : 0);
				if (getBlock(ax, ay, az) == GLASS)
					continue;
			}

			double hx = ox + dx * t, hy = oy + dy * t, hz = oz + dz * t;
			int texX, texY;
			if (axis == 1) {
				texX = (int) tex16(hx * 16);
				texY = (int) tex16(hz * 16);
				if (dy < 0.0)
					texY += 32;
			} else {
				texX = (int) tex16((hx + hz) * 16);
				texY = (int) tex16(hy * 16) + 16;
			}
			byte step = (byte) (axis == 0 ? sx : axis == 1 ? sy : sz);

			if (hoverPending) {
				hoverPending = false;
				if (t + tBase < reach) {
					newHoverX = bx;
					newHoverY = by;
					newHoverZ = bz;
					hoveredType = getType((byte) id);
					newDirX = axis == 0 ? -step : 0;
					newDirY = axis == 1 ? -step : 0;
					newDirZ = axis == 2 ? -step : 0;
				}
			}

			int raw = atlas[texX + texY * 16 + id * 768];
			boolean blockEdge = texX == 0 || (texY & 15) == 0 || texX == 15 || (texY & 15) == 15;
			boolean selectedEdge = primary && hl && !hideEverything && bx == hvX && by == hvY && bz == hvZ && blockEdge;
			// Draw the selection outline over transparent leaf texels too, so it stays a
			// continuous block-edge outline instead of tracing only the leaf texture.
			if ((raw & 0xFFFFFF) == 0 && !selectedEdge)
				continue; // Keep cutout transparency exact everywhere except the selection outline.
			int c;
			if (selectedEdge)
				c = 0xFFFFFF;
			else
				c = atlas[texX + texY * 16 + id * 768];
			final int bsg = breakStage;
			if (bsg >= 0 && !selectedEdge && bx == breakX && by == breakY && bz == breakZ)
				c = crackOverlay(c, texX, texY & 15, bsg);

			hT = t + tBase;
			hBx = bx;
			hBy = by;
			hBz = bz;
			hId = id;
			hAxis = axis;
			hSign = (byte) -step;
			hHx = hx;
			hHy = hy;
			hHz = hz;
			hR = (c >> 16 & 0xFF) / 255.0;
			hG = (c >> 8 & 0xFF) / 255.0;
			hB = (c & 0xFF) / 255.0;
			return true;
		}
		return false;
	}

	/** Per-frame fog setup: time-of-day tint for fog colors and the camera's own fog color. */
	static void prepareFog() {
		cave = Nexus.caveMix;
		if (cls) {
			fLR = fLG = fLB = 1;
		} else {
			double lv = 0.12 + 0.88 * smoothstep(-0.2, 0.35, -light.y);
			double m = Math.max(1e-3, Math.max(skyR, Math.max(skyG, skyB)));
			fLR = lv * (0.65 + 0.35 * skyR / m);
			fLG = lv * (0.65 + 0.35 * skyG / m);
			fLB = lv * (0.65 + 0.35 * skyB / m);
		}
		camFog.at(pbx, rpx, pby, rpy, pbz, rpz);
		fogCamR = camFog.r; fogCamG = camFog.g; fogCamB = camFog.b;
	}

	/**
	 * Detect highly perforated BRICKS/OAK_PLANKS structures such as the procedural Menger
	 * sponge. Their repeated tiny cavities make per-face AO and shadowing look noisy,
	 * so these local cells use a consistent, flat light level instead. Results are
	 * memoized per block and world/stream epoch; unloaded neighbours never count as air.
	 */
	private boolean flatPorousLighting(long x, long y, long z, int id) {
		if (id != BRICKS && id != OAK_PLANKS) return false;
		long epoch = ((long) Nexus.worldVer << 32) ^ (Nexus.streamVer & 0xFFFFFFFFL);
		long key = Memo.hash(x, y, z, epoch ^ 0x4D454E474552L);
		int cached = porousMemo.get(key);
		if (cached >= 0) return cached != 0;
		int air = 0, solidCount = 0;
		for (int dy = -1; dy <= 1; dy++) for (int dz = -1; dz <= 1; dz++) for (int dx = -1; dx <= 1; dx++) {
			if (dx == 0 && dy == 0 && dz == 0) continue;
			int q = probe(x + dx, y + dy, z + dz);
			if (q < 0) return false; // don't classify a structure against incomplete terrain
			int neighbour = q & 0xFF;
			if (neighbour == AIR) air++;
			else if (neighbour < OPAQUE.length && OPAQUE[neighbour]) solidCount++;
		}
		boolean porous = air >= 12 && solidCount >= 5;
		porousMemo.put(key, porous ? 1 : 0);
		return porous;
	}

	private void shadeClassic() {
	    final double hx = hHx, hy = hHy, hz = hHz;
	    final byte axis = hAxis, sign = hSign;

	    fogAt(hx, hy, hz);

	    final double ft = Math.min(1.0, hT * fog.dens / maxDist);

	    if (ft < FOG_SKIP && flatPorousLighting(hBx, hBy, hBz, hId)) {
	        final double flat = 0.78 * (1.0 - ft);
	        hR = hR * flat + fog.r * ft;
	        hG = hG * flat + fog.g * ft;
	        hB = hB * flat + fog.b * ft;
	        return;
	    }

	    double shade = (0xFF - (axis + 2) % 3 * 50) / 255.0;
	    shade *= 1.0 - ft;

	    if (ft < FOG_SKIP
	            && !fast
	            && lightQ >= 1
	            && AO_STRENGTH > 0.0
	            && withinAORange(hx, hy, hz)
	            && hId >= 0
	            && hId < OPAQUE.length
	            && OPAQUE[hId]) {

	        final long fx = hBx + (axis == 0 ? sign : 0);
	        final long fy = hBy + (axis == 1 ? sign : 0);
	        final long fz = hBz + (axis == 2 ? sign : 0);

	        shade *= faceAO(
	            hx, hy, hz, axis, fx, fy, fz,
	            AO_STRENGTH * 0.5
	        );
	    }

	    hR = hR * shade + fog.r * ft;
	    hG = hG * shade + fog.g * ft;
	    hB = hB * shade + fog.b * ft;
	}

	private void shadeModern() {
		// the skylight rays overwrite the h* fields, so copy everything first
		final double hx = hHx, hy = hHy, hz = hHz, t = hT, cr = hR, cg = hG, cb = hB;
		final byte axis = hAxis, sign = hSign, id = hId;
		final boolean fastTile = fast;
		final int q = fastTile ? 0 : lightQ;
		fogAt(hx, hy, hz);
		final double ft = Math.min(1, t * fog.dens / maxDist);
		final double gl = GLOW[id];

		if (ft >= FOG_SKIP) { // almost pure fog: flat ambient light is indistinguishable here
			hR = cr * (ambR * 0.55 + gl) * (1 - ft) + fog.r * ft;
			hG = cg * (ambG * 0.55 + gl) * (1 - ft) + fog.g * ft;
			hB = cb * (ambB * 0.55 + gl) * (1 - ft) + fog.b * ft;
			return;
		}

		final long fx = hBx + (axis == 0 ? sign : 0), fy = hBy + (axis == 1 ? sign : 0), fz = hBz + (axis == 2 ? sign : 0);
		if (flatPorousLighting(hBx, hBy, hBz, id)) {
			// Skip secondary sky/shadow/AO rays for the sponge and use one level on every face.
			hR = cr * (ambR * 0.85 + gl) * (1 - ft) + fog.r * ft;
			hG = cg * (ambG * 0.85 + gl) * (1 - ft) + fog.g * ft;
			hB = cb * (ambB * 0.85 + gl) * (1 - ft) + fog.b * ft;
			return;
		}

        double sky = 1, open = 1;
		// Ignore sky leakage in tall cave chambers while the camera is classified underground.
		if (cave > 0.5) { sky = 0; open = 0; }

		double sun = Math.max(0, sign * (axis == 0 ? lx : axis == 1 ? ly : lz));
		if (sun > 0.02) {
			if (fastTile) sun *= 0.6;                       // placeholder until this tile is refined
			else if (open < 0.05) sun = 0;                  // fully roofed over: no direct outside light
			else if (inShadow(hx, hy, hz, axis, sign, fx, fy, fz, t, open < 0.9)) sun = 0;
		}

		double ao = 1.0;

		if (AO_STRENGTH > 0.0
		        && q >= 1
		        && id >= 0
		        && id < OPAQUE.length
		        && OPAQUE[id]
		        && withinAORange(hx, hy, hz)) {

		    ao = faceAO(
		        hx, hy, hz, axis, fx, fy, fz,
		        AO_STRENGTH
		    );
		}

		final double enclosed = 1 - smoothstep(0.0, 0.85, sky);
		final double shade = Math.max(cave, 0.35 * enclosed);
		sky = Math.max(0.78 + (CAVE_SKY_MIN - 0.78) * shade, sky);
		double softAO = 1.0 - (1.0 - ao) * 0.55;
		double base = 0.18 + (CAVE_AMB_BASE - 0.18) * shade;
		double amb = (base + (1.0 - base) * sky) * softAO;
		double k = sun * 0.55 * (0.78 + 0.22 * softAO);
		double lamp = lanternEnabled && !classic ? (1 - sky) * Math.max(0, 1 - t / 18.0) * 0.7 : 0;

		double bR = 0, bG = 0, bB = 0;
		if (Nexus.blockLightingEnabled && q >= 1) { blockLight(fx, fy, fz, t); bR = blR; bG = blG; bB = blB; }

		double lr = ambR * amb + sunR * k + lamp + bR;
		double lg = ambG * amb + sunG * k + lamp * 0.8 + bG;
		double lb = ambB * amb + sunB * k + lamp * 0.5 + bB;

		hR = cr * (lr + gl) * (1 - ft) + fog.r * ft;
		hG = cg * (lg + gl) * (1 - ft) + fog.g * ft;
		hB = cb * (lb + gl) * (1 - ft) + fog.b * ft;
	}

	private boolean solid(long x, long y, long z) {
		int p = probe(x, y, z);
		if (p < 0) return false;
		int id = p & 0xFF;
		return id < OPAQUE.length && OPAQUE[id];
	}

	private double faceAO(double hx, double hy, double hz, byte axis, long fx, long fy, long fz, double strength) {
	    if (strength <= 0.0) return 1.0;

	    final double u = axis == 0 ? hy : hx;
	    final double v = axis == 2 ? hy : hz;
	    final double fu = u - Math.floor(u);
	    final double fv = v - Math.floor(v);

	    final double sample = Math.max(
	        0.02, Math.min(1.0, aoAt(fx, fy, fz, axis, fu, fv))
	    );

	    return strength == 1.0 ? sample : Math.max(0.02, Math.pow(sample, strength));
	}

	private boolean withinAORange(double x, double y, double z) {
	    final double dx = x - px;
	    final double dy = y - py;
	    final double dz = z - pz;

	    return dx * dx + dy * dy + dz * dz <= 16384.0;
	}

	private double aoAt(long x, long y, long z, byte a, double fu, double fv) {
	    final int um, up, vm, vp;

	    switch (a) {
	        case 0:
	            um = solid(x, y - 1, z) ? 1 : 0;
	            up = solid(x, y + 1, z) ? 1 : 0;
	            vm = solid(x, y, z - 1) ? 1 : 0;
	            vp = solid(x, y, z + 1) ? 1 : 0;
	            break;
	        case 1:
	            um = solid(x - 1, y, z) ? 1 : 0;
	            up = solid(x + 1, y, z) ? 1 : 0;
	            vm = solid(x, y, z - 1) ? 1 : 0;
	            vp = solid(x, y, z + 1) ? 1 : 0;
	            break;
	        default:
	            um = solid(x - 1, y, z) ? 1 : 0;
	            up = solid(x + 1, y, z) ? 1 : 0;
	            vm = solid(x, y - 1, z) ? 1 : 0;
	            vp = solid(x, y + 1, z) ? 1 : 0;
	            break;
	    }

	    final int a00 = cornerAO(x, y, z, a, -1, -1, um, vm);
	    final int a10 = cornerAO(x, y, z, a,  1, -1, up, vm);
	    final int a01 = cornerAO(x, y, z, a, -1,  1, um, vp);
	    final int a11 = cornerAO(x, y, z, a,  1,  1, up, vp);

	    final double lo = a00 + (a10 - a00) * fu;
	    final double hi = a01 + (a11 - a01) * fu;
	    return (lo + (hi - lo) * fv) / 3.0;
	}

	private int cornerAO(long x, long y, long z, byte axis, int i, int j, int s1, int s2) {
	    if (s1 == 1 && s2 == 1) {
	        return 0;
	    }

	    final boolean c;
	    switch (axis) {
	        case 0: c = solid(x, y + i, z + j); break;
	        case 1: c = solid(x + i, y, z + j); break;
	        default: c = solid(x + i, y + j, z); break;
	    }

	    return 3 - (s1 + s2 + (c ? 1 : 0));
	}

	static final double SKY_FADE = 15;
	// Keep skylight directional: one vertical ray per sample. Lateral rays caused
	// skylight leakage around corners and made AO appear inconsistent.
	private static final double[][] SKY_OFFSETS = { { 0, 0, 1 } }; // {dx, dz, weight}

	private final Memo skyMemo = new Memo(32768), shMemo = new Memo(16384), porousMemo = new Memo(8192);

	/** One vertical sky ray from the middle of (cx, fy, cz). Payload 255 = open sky, otherwise contribution * 250. */
	private int skyRay(long cx, long fy, long cz) {
	    long epoch = ((long) Nexus.worldVer << 32) ^ (Nexus.streamVer & 0xFFFFFFFFL);
	    long key = Memo.hash(cx, fy, cz, epoch ^ 13L);
	    int p = skyMemo.get(key);
	    if (p >= 0) return p;
	    boolean blocked = march((cx - pbx) + 0.5, (fy - pby) + 0.5, (cz - pbz) + 0.5, 0, -1, 0, SKY_RAY, false, false);
	    if (blocked) p = (int) Math.round(Math.min(1, hT / 24.0) * 0.5 * 250);
	    else if (hUnloaded && cave > 0.5) p = 125;
	    else p = 255;
	    // A ray that ended at an unloaded chunk is only a temporary estimate.
	    // Avoid caching it so the proper skylight is calculated once terrain arrives.
	    if (hUnloaded) skyUnloaded = true;
	    else skyMemo.put(key, p);
	    return p;
	}

	private double skyLight(long fx, long fy, long fz) {
	    long epoch = ((long) Nexus.worldVer << 32) ^ (Nexus.streamVer & 0xFFFFFFFFL);
	    long key = Memo.hash(fx, fy, fz, epoch), key2 = Memo.hash(fx, fy, fz, epoch ^ 7L);
	    int c = skyMemo.get(key), o = skyMemo.get(key2);
	    if (c >= 0 && o >= 0) {
	        skyOpen = o / 255.0;
	        return c / 255.0;
	    }
	    double total = 0, wsum = 0, openW = 0;
	    skyUnloaded = false;
	    for (double[] off : SKY_OFFSETS) {
	        long cx = fx + (long) off[0], cz = fz + (long) off[1];
	        double w = off[2];
	        if (w != 2 && solid(cx, fy, cz)) continue; // lateral sample starts inside rock
	        int p = skyRay(cx, fy, cz);
	        wsum += w;
	        if (p == 255) { total += w; openW += w; } else total += w * p / 250.0;
	    }
	    int q = (int) Math.round(total / wsum * 255);
	    skyOpen = openW / wsum;
	    // If any sample was incomplete, don't preserve the blended result either.
	    if (!skyUnloaded) {
	        skyMemo.put(key, q);
	        skyMemo.put(key2, (int) Math.round(skyOpen * 255));
	    }
	    return q / 255.0;
	}

	/** fog.at() for a hit; neighbouring pixels landing in the same quarter-block reuse the result. */
	private void fogAt(double hx, double hy, double hz) {
		long qx = cellIdx(pbx, hx, 4), qy = cellIdx(pby, hy, 4), qz = cellIdx(pbz, hz, 4);
		if (qx == fqx && qy == fqy && qz == fqz && fogSeen == fogStamp)
			return;
		fog.at(pbx, hx, pby, hy, pbz, hz);
		fqx = qx; fqy = qy; fqz = qz; fogSeen = fogStamp;
	}
}

/** Fixed-capacity struct-of-arrays particle pool. Main thread only. World +y is down, so "up" is negative vy. */
final class Particles {
	static final int CAP = 65536;
	static int cap = 2048;
	static final double GRAVITY = 0.002, DRAG = 0.995;
	static double[] pX = new double[cap], pY = new double[cap], pZ = new double[cap];
	static double[] vX = new double[cap], vY = new double[cap], vZ = new double[cap];
	static float[] size = new float[cap];
	static int[] color = new int[cap], life = new int[cap];
	static int count, overwrite;
	static final Random R = new Random();
	static long oX, oY, oZ;
	private static final long REBASE = 1L << 20;

	static void clear() {
		count = 0;
	}

	private static void grow() {
		int nc = Math.min(CAP, cap << 1);
		pX = Arrays.copyOf(pX, nc); pY = Arrays.copyOf(pY, nc); pZ = Arrays.copyOf(pZ, nc);
		vX = Arrays.copyOf(vX, nc); vY = Arrays.copyOf(vY, nc); vZ = Arrays.copyOf(vZ, nc);
		size = Arrays.copyOf(size, nc); color = Arrays.copyOf(color, nc); life = Arrays.copyOf(life, nc);
		cap = nc;
	}

	private static void anchor(long bx, long by, long bz) {
		if (count == 0) { oX = bx; oY = by; oZ = bz; return; }
		long dx = bx - oX, dy = by - oY, dz = bz - oZ;
		if (Math.abs(dx) < REBASE && Math.abs(dy) < REBASE && Math.abs(dz) < REBASE)
			return;
		for (int i = 0; i < count; i++) { pX[i] -= dx; pY[i] -= dy; pZ[i] -= dz; }
		oX = bx; oY = by; oZ = bz;
	}

	/** Position = block (bx,by,bz) + offset (fx,fy,fz); offsets may stray outside 0..1. */
	static void spawn(long bx, long by, long bz, double fx, double fy, double fz, double vx, double vy, double vz, int rgb, double sz2, int ttl) {
		anchor(bx, by, bz);
		int i;
		if (count < cap) {
			i = count++;
		} else if (cap < CAP) {
			grow();
			i = count++;
		} else {
			i = overwrite;
			overwrite = (overwrite + 1) & (CAP - 1);
		}
		pX[i] = (bx - oX) + fx; pY[i] = (by - oY) + fy; pZ[i] = (bz - oZ) + fz;
		vX[i] = vx; vY[i] = vy; vZ[i] = vz;
		color[i] = rgb;
		size[i] = (float) sz2;
		life[i] = ttl;
	}

	static int sample(int id) {
		for (byte t = 0; t < 24; t++) {
			int c = atlas[R.nextInt(16) + (16 + R.nextInt(16)) * 16 + id * 768];
			if ((c >>> 24) != 0 && (c & 0xFFFFFF) != 0) {
				double s = 0.7 + R.nextDouble() * 0.3;
				return (int) ((c >> 16 & 0xFF) * s) << 16 | (int) ((c >> 8 & 0xFF) * s) << 8 | (int) ((c & 0xFF) * s);
			}
		}
		switch (id) {
		case Nexus.LEAVES: return 0x398A32;
		case Nexus.RED_LEAVES: return 0xB52D24;
		case Nexus.ORANGE_LEAVES: return 0xD97818;
		case Nexus.YELLOW_LEAVES: return 0xC9AD1B;
		default: return 0;
		}
	}

	static void burst(long bx, long by, long bz, byte id, int n, double speed) {
		if (id == AIR)
			return;
		for (int i = 0; i < n; i++)
			spawn(bx, by, bz, R.nextDouble(), R.nextDouble(), R.nextDouble(),
					(R.nextDouble() - 0.5) * speed, (R.nextDouble() - 0.8) * speed, (R.nextDouble() - 0.5) * speed,
					sample(id), 0.08 + R.nextDouble() * 0.08, 60 + R.nextInt(80));
	}

	private static double sprintDistance;

	static void sprintTrail(byte below, double moved) {
		if (!Nexus.sprint || below == AIR || moved < 1e-4) {
			if (!Nexus.sprint || below == AIR)
				sprintDistance = 0;
			return;
		}
		sprintDistance += moved;
		if (sprintDistance < 0.22)
			return;
		sprintDistance %= 0.22;

		double dx = Nexus.diff(Nexus.x, Nexus.prevX), dz = Nexus.diff(Nexus.z, Nexus.prevZ);
		double len = Math.max(1e-6, Math.hypot(dx, dz));
		long bx = Nexus.floorOf(Nexus.x), by = Nexus.floorOf(Nexus.y), bz = Nexus.floorOf(Nexus.z);
		double fx = Nexus.fracOf(Nexus.x), fy = Nexus.fracOf(Nexus.y), fz = Nexus.fracOf(Nexus.z);
		for (byte n = 0; n < 2; n++) {
			double spreadX = (R.nextDouble() - 0.5) * 0.018;
			double spreadZ = (R.nextDouble() - 0.5) * 0.018;
			spawn(bx, by, bz,
				fx + (R.nextDouble() - 0.5) * 0.42,
				fy + 1.48 + R.nextDouble() * 0.05,
				fz + (R.nextDouble() - 0.5) * 0.42,
				-dx / len * (0.012 + R.nextDouble() * 0.012) + spreadX,
				-0.012 - R.nextDouble() * 0.012,
				-dz / len * (0.012 + R.nextDouble() * 0.012) + spreadZ,
				sample(below), 0.025 + R.nextDouble() * 0.035, 12 + R.nextInt(13));
		}
	}

	static void debris(long bx, long by, long bz, byte id, long cx, long cy, long cz) {
		if (id == AIR || R.nextInt(3) != 0)
			return;
		double dx = (bx - cx) + 0.5, dy = (by - cy) + 0.5, dz = (bz - cz) + 0.5;
		double len = Math.sqrt(dx * dx + dy * dy + dz * dz) + 1e-6;
		double s = 0.03 + R.nextDouble() * 0.05;
		spawn(bx, by, bz, 0.5, 0.5, 0.5, dx / len * s, dy / len * s - 0.02, dz / len * s, sample(id), 0.1 + R.nextDouble() * 0.1, 80 + R.nextInt(100));
	}

	private static long qx = Long.MIN_VALUE, qy, qz;
	private static Octree qc; // chunk cache, valid for one update() pass

	private static boolean solidAt(long bx, long by, long bz) {
		long cx = bx >> SHIFT, cy = by >> SHIFT, cz = bz >> SHIFT;
		if (cx != qx || cy != qy || cz != qz) {
			qx = cx; qy = cy; qz = cz;
			qc = world.chunk(cx, cy, cz);
		}
		Octree c = qc;
		if (c == null || c == World.UNLOADED)
			return false;
		return c.get((byte) (bx & MASK), (byte) (by & MASK), (byte) (bz & MASK)) != AIR;
	}

	/** x/y/z are particle-local coordinates (relative to the origin block). */
	private static boolean solid(double x, double y, double z) {
		return solidAt(oX + (long) Math.floor(x), oY + (long) Math.floor(y), oZ + (long) Math.floor(z));
	}

	static void update() {
		qx = Long.MIN_VALUE; // invalidate cache: chunks may have changed since last tick
		for (int i = 0; i < count;) {
			if (--life[i] <= 0) {
				remove(i);
				continue;
			}
			double x = pX[i], y = pY[i], z = pZ[i];
			double vx = vX[i] * DRAG, vz = vZ[i] * DRAG, vy = vY[i] * DRAG + GRAVITY;

			double nx = x + vx; // only test blocks when the particle enters a new cell
			if (Math.floor(nx) != Math.floor(x) && solid(nx, y, z)) vx = -vx * 0.4; else x = nx;
			double nz = z + vz;
			if (Math.floor(nz) != Math.floor(z) && solid(x, y, nz)) vz = -vz * 0.4; else z = nz;
			double ny = y + vy;
			if (Math.floor(ny) != Math.floor(y) && solid(x, ny, z)) {
				if (vy > 0) { vx *= 0.7; vz *= 0.7; }
				vy = Math.abs(vy) < 0.006 ? 0 : -vy * 0.4;
			} else y = ny;

			pX[i] = x; pY[i] = y; pZ[i] = z;
			vX[i] = vx; vY[i] = vy; vZ[i] = vz;
			i++;
		}
		trim();
	}

	static void render() {
		if (count == 0)
			return;
		final int[] out = Render.out;
		final float[] depth = Render.depth;
		final int w = Render.w, h = Render.h;
		final double syw = sinYaw, cyw = cosYaw, sp = sinPitch, cp = cosPitch;
		final double invXS = 1.0 / Render.xScale, invYS = 1.0 / Render.yScale;
		final double maxK = dist; // beyond the fog distance nothing is visible anyway
		final double offX = oX - Render.pbx, offY = oY - Render.pby, offZ = oZ - Render.pbz; // origin relative to the camera block
		final Render lr = (!classic && !workers.isEmpty()) ? workers.get(0) : null;
		if (lr != null) lr.beginParticleLight();
		for (int i = 0; i < count; i++) {
			double rx = offX + pX[i] - Render.rpx, ry = offY + pY[i] - Render.rpy, rz = offZ + pZ[i] - Render.rpz;
			double zc = rz * cyw + rx * syw, xc = rx * cyw - rz * syw;
			double k = zc * cp - ry * sp;
			if (k < 0.1 || k > maxK)
				continue;
			double scrX = xc / k * invXS + w * 0.5;
			double scrY = (ry * cp + zc * sp) / k * invYS + h * 0.5;
			double half = size[i] * Math.min(1.0, life[i] / 20.0) * 0.5 / k;
			int hx = Math.min(12, Math.max(1, (int) Math.round(half * invXS)));
			int hy = Math.min(12, Math.max(1, (int) Math.round(half * invYS)));
			int cx = (int) Math.floor(scrX), cy = (int) Math.floor(scrY);
			if (cx + hx < 0 || cx - hx >= w || cy + hy < 0 || cy - hy >= h)
				continue; // off-screen: skip before the sqrt
			int x0 = Math.max(0, cx - hx), x1 = Math.min(w - 1, cx + hx);
			int y0 = Math.max(0, cy - hy), y1 = Math.min(h - 1, cy + hy);
			float d = (float) Math.sqrt(rx * rx + ry * ry + rz * rz);
			int col = color[i];
			if (lr != null) col = lr.litParticle(col, oX + (long) Math.floor(pX[i]), oY + (long) Math.floor(pY[i]), oZ + (long) Math.floor(pZ[i]), k);
			for (int yy = y0; yy <= y1; yy++) {
				int row = yy * w;
				for (int xx = x0; xx <= x1; xx++)
					if (d < depth[row + xx])
						out[row + xx] = col;
			}
		}
	}

	private static void remove(int i) {
		int l = --count;
		if (i == l)
			return;
		pX[i] = pX[l]; pY[i] = pY[l]; pZ[i] = pZ[l];
		vX[i] = vX[l]; vY[i] = vY[l]; vZ[i] = vZ[l];
		size[i] = size[l]; color[i] = color[l]; life[i] = life[l];
	}

	private static int idle;
	/** Halves the pool every ~5 s while it is mostly empty. */
	static void trim() {
	    if (cap <= 2048 || count > cap / 8) { idle = 0; return; }
	    if (++idle < 500) return;
	    idle = 0;
	    int nc = cap >> 1;
	    pX = Arrays.copyOf(pX, nc); pY = Arrays.copyOf(pY, nc); pZ = Arrays.copyOf(pZ, nc);
	    vX = Arrays.copyOf(vX, nc); vY = Arrays.copyOf(vY, nc); vZ = Arrays.copyOf(vZ, nc);
	    size = Arrays.copyOf(size, nc); color = Arrays.copyOf(color, nc); life = Arrays.copyOf(life, nc);
	    cap = nc;
	    if (overwrite >= nc) overwrite = 0;
	}
}

final class Vec3 {
	double x, y, z;

	Vec3(double val) {
		x = y = z = val;
	}

	Vec3(double x, double y, double z) {
		this.x = x;
		this.y = y;
		this.z = z;
	}

	static Vec3 lerp(Vec3 a, Vec3 b, double t, Vec3 out) {
		out.x = a.x + (b.x - a.x) * t;
		out.y = a.y + (b.y - a.y) * t;
		out.z = a.z + (b.z - a.z) * t;
		return out;
	}

	static Vec3 rgb(int rgb) {
		return new Vec3(((rgb >> 16) & 0xFF) / 255.0, ((rgb >> 8) & 0xFF) / 255.0, (rgb & 0xFF) / 255.0);
	}
}

final class Fog {
	double r, g, b, dens; // result of the last at()
	// rgb + density: none, moss, snow, obsidian, crystal, basalt (indexed by CB_*)
	private static final double[][] CAVE = {
		{ .03, .04, .06, 2.4 }, { .10, .34, .14, 2.0 }, { .45, .65, .90, 1.6 }, { .17, .06, .28, 2.4 }, { .03, .04, .06, 2.4 }, { .10, .08, .07, 2.8 } };
	private static final int[] ASC = { CB_MOSS, CB_SNOW, CB_BASALT, CB_OBSIDIAN, CB_CRYSTAL }; // ascending priority
	private static final int N = 8192;
	private final long[] keys = new long[N];
	private final double[] cache = new double[N * 4];
	private double sr, sg, sb, sd;
	private final double[] caveBlend = new double[4];
	// Per-renderer cache of biome-noise lattice samples. Interpolation keeps the
	// tint continuous while avoiding a full noise evaluation for every pixel.
	private static final int BIOME_CACHE_SIZE = 4096;
	private final long[] biomeX = new long[BIOME_CACHE_SIZE], biomeZ = new long[BIOME_CACHE_SIZE];
	private final double[] biomeNoise = new double[BIOME_CACHE_SIZE];
	private final boolean[] biomeUsed = new boolean[BIOME_CACHE_SIZE];

	Fog() { Arrays.fill(keys, World.NONE); }

	/** Cached lattice samples plus bilinear interpolation: smooth across cells, cheap per pixel. */
	private double biomeSample(long gx, long gz) {
		long h = gx * 0x9E3779B97F4A7C15L ^ Long.rotateLeft(gz * 0xC2B2AE3D27D4EB4FL, 29);
		int i = (int) (h ^ (h >>> 32)) & (BIOME_CACHE_SIZE - 1);
		if (biomeUsed[i] && biomeX[i] == gx && biomeZ[i] == gz)
			return biomeNoise[i];
		double v = Nexus.biomeVal(gx * 16.0, gz * 16.0);
		biomeUsed[i] = true; biomeX[i] = gx; biomeZ[i] = gz; biomeNoise[i] = v;
		return v;
	}

	private void surface(long bx, double ox, long bz, double oz) {
		double fox = Math.floor(ox), foz = Math.floor(oz);
		long ix = bx + (long) fox, iz = bz + (long) foz;
		long gx = Math.floorDiv(ix, 16L), gz = Math.floorDiv(iz, 16L);
		double fx = ((ix - gx * 16) + (ox - fox)) / 16.0, fz = ((iz - gz * 16) + (oz - foz)) / 16.0;
		fx = fx * fx * (3 - 2 * fx);
		fz = fz * fz * (3 - 2 * fz);
		double a = biomeSample(gx, gz), b = biomeSample(gx + 1, gz);
		double c = biomeSample(gx, gz + 1), d = biomeSample(gx + 1, gz + 1);
		double v = (a + (b - a) * fx) + ((c + (d - c) * fx) - (a + (b - a) * fx)) * fz;
		double dry = 1 - smoothstep(0.55, 0.75, v);
		double ice = smoothstep(1.75, 1.95, v);
		double snow = smoothstep(1.3, 1.5, v) * (1 - ice);
		double plain = Math.max(0, 1 - dry - snow - ice);
		sr = dry * .85 + plain * Nexus.red   + snow * .82 + ice * .55;
		sg = dry * .72 + plain * Nexus.green + snow * .90 + ice * .82;
		sb = dry * .48 + plain * Nexus.blue  + snow * .97 + ice * 1.0;
		sd = dry * 1.0 + plain * 1.0 + snow * 1.3 + ice * 1.7;
	}

	private double[] cave(long bx, double ox, long by, double oy, long bz, double oz) {
		double gx = ox - 0.5, gy = oy - 0.5, gz = oz - 0.5;
		double flx = Math.floor(gx), fly = Math.floor(gy), flz = Math.floor(gz);
		long x0 = bx + (long) flx, y0 = by + (long) fly, z0 = bz + (long) flz;
		double fx = gx - flx, fy = gy - fly, fz = gz - flz;
		double[] out = caveBlend;
		Arrays.fill(out, 0.0);
		for (byte dx = 0; dx <= 1; dx++)
			for (byte dy = 0; dy <= 1; dy++)
				for (byte dz = 0; dz <= 1; dz++) {
					double w = (dx == 0 ? 1 - fx : fx) * (dy == 0 ? 1 - fy : fy) * (dz == 0 ? 1 - fz : fz);
					int o = caveVoxel(x0 + dx, y0 + dy, z0 + dz);
					for (byte j = 0; j < 4; j++) out[j] += cache[o + j] * w;
				}
		return out;
	}

	/** Fog colour and density at block (bx,by,bz) plus an offset (ox,oy,oz) that may stray outside 0..1. */
	void at(long bx, double ox, long by, double oy, long bz, double oz) {
		surface(bx, ox, bz, oz);
		r = sr * Render.fLR; g = sg * Render.fLG; b = sb * Render.fLB; dens = sd;
		double c = Render.cave;
		if (c > 0.002) {
			double[] k = cave(bx, ox, by, oy, bz, oz);
			r += (k[0] - r) * c; g += (k[1] - g) * c; b += (k[2] - b) * c; dens += (k[3] - dens) * c;
		}
	}

	private int caveVoxel(long x, long y, long z) {
		long k = World.key(x, y, z);
		int i = (int) ((k * 0x9E3779B97F4A7C15L) >>> 51); // 13 bits
		int o = i << 2;
		if (keys[i] != k) {
			keys[i] = k;
			System.arraycopy(CAVE[0], 0, cache, o, 4);
			for (int b : ASC) {
				double w = Nexus.zone(b, x, y, z);
				if (w > 0)
					for (int j = 0; j < 4; j++)
						cache[o + j] += (CAVE[b][j] - cache[o + j]) * w;
			}
			int basinBiome = Nexus.basinFogBiome(x, y, z);
			if (basinBiome != CB_NONE) {
				double w = Nexus.basinFogWeight(x, y, z);
				for (int j = 0; j < 4; j++)
					cache[o + j] += (CAVE[basinBiome][j] - cache[o + j]) * w;
			}
		}
		return o;
	}
}

final class Octree {
	static final int LEAF = 0x80000000, PACKED = 0xC0000000, PBIT = 0x40000000, PMASK = 0x3FFFFFFF;
	static final long ONES = 0x0101010101010101L;
	static final int[] EMPTY_I = new int[0];
	static final long[] EMPTY_L = new long[0];
	private static final int[] OFF = { 0, 1, 64, 65, 4096, 4097, 4160, 4161 };
	private static final int[] P_BLOCK = new int[8], P_ENTRY = new int[8]; // main-thread edits only
	private static final Octree[] UNIFORM = new Octree[256];
	private static final ThreadLocal<Octree> SCRATCH = ThreadLocal.withInitial(() -> new Octree(2048));
	private static final ThreadLocal<int[][]> SC = ThreadLocal.withInitial(() -> new int[7][8]);
	static {
		for (int i = 0; i < 256; i++) {
			Octree o = new Octree(0);
			o.root = LEAF | i;
			o.shared = true;
			UNIFORM[i] = o;
		}
	}

	int[] n;
	long[] cells = EMPTY_L;
	int root = LEAF; // LEAF = all air
	int top, free = -1, ctop, cfree = -1;
	boolean shared;  // immutable shared uniform chunk: copy() before editing
	int ver; private java.lang.ref.SoftReference<Octree> froze; private int frozeVer = -1;

	Octree(int cap) { n = cap == 0 ? EMPTY_I : new int[cap]; }

	static Octree uniform(int id) { return UNIFORM[id & 0xFF]; }

	boolean isEmpty() { return root == LEAF; }

	int memoryBytes() { return n.length * 4 + cells.length * 8 + 48; }

	/** Fresh editable copy of a shared uniform chunk. */
	Octree copy() {
		Octree o = new Octree(64);
		o.root = root;
		return o;
	}

	/** Drop spare capacity (call when a chunk goes to cold storage). */
	void compact() {
		if (top < n.length) n = Arrays.copyOf(n, top);
		if (ctop < cells.length) cells = ctop == 0 ? EMPTY_L : Arrays.copyOf(cells, ctop);
	}

	void reset() {
		root = LEAF; top = 0; free = -1; ctop = 0; cfree = -1;
	}

	/** Block at local coordinates (0..63). */
	byte get(byte x, byte y, byte z) {
		int v = root, sh = 6;
		final int[] a = n;
		while (v >= 0) {
			sh--;
			v = a[v + (((x >> sh) & 1) | (((y >> sh) & 1) << 1) | (((z >> sh) & 1) << 2))];
		}
		if ((v & PBIT) != 0)
			return (byte) (cells[v & PMASK] >>> (((x & 1) | ((y & 1) << 1) | ((z & 1) << 2)) << 3));
		return (byte) v;
	}

	/**
	 * Uniform cube containing the voxel: returns (log2 size << 8 | id) (>= 0),
	 * or the raw PACKED entry (< 0) when the voxel lies in a mixed 2x2x2 cell.
	 */
	int find(int x, int y, int z) {
		int v = root, lg = 6;
		final int[] a = n;
		while (v >= 0) {
			lg--;
			v = a[v + (((x >> lg) & 1) | (((y >> lg) & 1) << 1) | (((z >> lg) & 1) << 2))];
		}
		if ((v & PBIT) != 0)
			return v;
		return lg << 8 | (v & 0xFF);
	}

	private int alloc(int v) {
		int b;
		if (free >= 0) {
			b = free;
			free = n[b];
		} else {
			b = top;
			top += 8;
			if (top > n.length)
				n = Arrays.copyOf(n, Math.max(64, n.length * 2));
		}
		Arrays.fill(n, b, b + 8, v);
		return b;
	}

	private void release(int b) {
		n[b] = free;
		free = b;
	}

	private int allocCell(long v) {
		int i;
		if (cfree >= 0) {
			i = cfree;
			cfree = (int) cells[i];
		} else {
			i = ctop++;
			if (i >= cells.length)
				cells = Arrays.copyOf(cells, Math.max(16, cells.length * 2));
		}
		cells[i] = v;
		return i;
	}

	private void releaseCell(int i) {
		cells[i] = cfree;
		cfree = i;
	}

	/** Sets a voxel; splits uniform leaves on demand and re-merges uniform siblings. Returns true if changed. */
	boolean set(int x, int y, int z, byte b) {
		ver++;
		final int id = b & 0xFF, lv = LEAF | id;
		if (root < 0) {
			if (root == lv) return false;
			root = alloc(root);
		}
		int node = root, entry = -1, d = 0, sh = 5;
		for (;;) {
			P_BLOCK[d] = node;
			P_ENTRY[d] = entry;
			d++;
			int idx = node + (((x >> sh) & 1) | (((y >> sh) & 1) << 1) | (((z >> sh) & 1) << 2));
			int v = n[idx];
			if (v >= 0) {
				node = v; entry = idx; sh--;
				continue;
			}
			int sub = ((x & 1) | ((y & 1) << 1) | ((z & 1) << 2)) << 3;
			if ((v & PBIT) != 0) { // edit inside a packed cell
				int ci = v & PMASK;
				long old = cells[ci];
				if (((old >>> sub) & 0xFF) == id) return false;
				long nv = (old & ~(0xFFL << sub)) | ((long) id << sub);
				if (nv != (nv & 0xFF) * ONES) {
					cells[ci] = nv;
					return true;
				}
				releaseCell(ci); // became uniform again
				n[idx] = LEAF | (int) (nv & 0xFF);
				break;
			}
			if (v == lv) return false;
			if (sh == 1) { // uniform 2x2x2 leaf -> packed cell
				long base = (long) (v & 0xFF) * ONES;
				long nv = (base & ~(0xFFL << sub)) | ((long) id << sub);
				n[idx] = PACKED | allocCell(nv);
				return true;
			}
			int c = alloc(v);
			n[idx] = c;
			node = c; entry = idx; sh--;
		}
		for (int i = d - 1; i >= 0; i--) { // merge uniform blocks back into leaves
			int blk = P_BLOCK[i], f = n[blk];
			if (f >= 0 || (f & PBIT) != 0)
				break;
			boolean same = true;
			for (int k = 1; k < 8; k++)
				if (n[blk + k] != f) { same = false; break; }
			if (!same)
				break;
			release(blk);
			if (P_ENTRY[i] < 0) root = f; else n[P_ENTRY[i]] = f;
		}
		return true;
	}

	/** Compress a dense chunk (index = x | y<<6 | z<<12). null = entirely air; uniform chunks are shared. */
	static Octree build(byte[] d) {
		Octree s = SCRATCH.get();
		s.reset();
		int r = s.make(d, 0, 0, 0, 6, SC.get());
		Octree res;
		if (r < 0) {
			int id = r & 0xFF;
			res = id == 0 ? null : uniform(id);
		} else {
			res = new Octree(0);
			res.root = r;
			res.n = Arrays.copyOf(s.n, s.top);
			res.cells = s.ctop == 0 ? EMPTY_L : Arrays.copyOf(s.cells, s.ctop);
			res.top = s.top;
			res.ctop = s.ctop;
		}
		if (s.n.length > 65536) s.n = new int[2048];
		if (s.cells.length > 8192) s.cells = EMPTY_L;
		return res;
	}

	private int make(byte[] d, int x, int y, int z, int lg, int[][] sc) {
		if (lg == 1) {
			int base = x | (y << 6) | (z << 12);
			byte f = d[base];
			if (d[base + 1] == f && d[base + 64] == f && d[base + 65] == f && d[base + 4096] == f
					&& d[base + 4097] == f && d[base + 4160] == f && d[base + 4161] == f)
				return LEAF | (f & 0xFF);
			long p = 0;
			for (int i = 0; i < 8; i++)
				p |= (long) (d[base + OFF[i]] & 0xFF) << (i << 3);
			return PACKED | allocCell(p);
		}
		int[] c = sc[lg];
		int h = 1 << (lg - 1);
		for (int i = 0; i < 8; i++)
			c[i] = make(d, x + ((i & 1) != 0 ? h : 0), y + ((i & 2) != 0 ? h : 0), z + ((i & 4) != 0 ? h : 0), lg - 1, sc);
		int f = c[0];
		boolean uni = f < 0 && (f & PBIT) == 0;
		for (int k = 1; k < 8 && uni; k++)
			if (c[k] != f) uni = false;
		if (uni)
			return f;
		int b = alloc(0);
		System.arraycopy(c, 0, n, b, 8);
		return b;
	}

	/** Expand into a dense array (length 64^3). */
	void toDense(byte[] out) {
		Arrays.fill(out, (byte) 0);
		expand(root, 0, 0, 0, 64, out);
	}

	private void expand(int v, int x, int y, int z, int size, byte[] out) {
		if (v < 0) {
			if ((v & PBIT) != 0) {
				long p = cells[v & PMASK];
				for (int i = 0; i < 8; i++) {
					byte id = (byte) (p >>> (i << 3));
					if (id != 0)
						out[(x + (i & 1)) | ((y + ((i >> 1) & 1)) << 6) | ((z + ((i >> 2) & 1)) << 12)] = id;
				}
				return;
			}
			byte id = (byte) v;
			if (id == 0) return;
			for (int zz = z; zz < z + size; zz++)
				for (int yy = y; yy < y + size; yy++) {
					int b = x | (yy << 6) | (zz << 12);
					Arrays.fill(out, b, b + size, id);
				}
			return;
		}
		int h = size >> 1;
		for (int i = 0; i < 8; i++)
			expand(n[v + i], x + ((i & 1) != 0 ? h : 0), y + ((i & 2) != 0 ? h : 0), z + ((i & 4) != 0 ? h : 0), h, out);
	}

	Octree frozen() {
		if (shared) return this;
		Octree f = froze == null ? null : froze.get();
		if (f != null && frozeVer == ver) return f; // unchanged since last snapshot: reuse
		Octree o = new Octree(0);
		o.root = root;
		o.top = top;
		o.ctop = ctop;
		o.n = Arrays.copyOf(n, top);
		o.cells = ctop == 0 ? EMPTY_L : Arrays.copyOf(cells, ctop);
		froze = new java.lang.ref.SoftReference<>(o);
		frozeVer = ver;
		return o;
	}

	private int glowVer = -1;
	private boolean glowFlag;

	/** True if the chunk may hold an emitting block. Conservative: freed nodes can give a false positive, never a false negative. */
	boolean mayGlow(float[] glow) {
	    if (glowVer == ver) return glowFlag;
	    boolean f = false;
	    if (root < 0) {
	        int id = root & 0xFF; f = id < glow.length && glow[id] > 0;
	    } else {
	        int nodeLimit = Math.max(0, Math.min(top, n == null ? 0 : n.length));
	        for (int i = 0; i < nodeLimit && !f; i++) {
	            int v = n[i];
	            if (v >= 0) continue;
	            if ((v & PBIT) != 0) {
                    int ci = v & PMASK;
                    if (cells == null || ci < 0 || ci >= cells.length) continue; // ignore stale/corrupt packed-cell references
	                long p = cells[ci];
	                for (int k = 0; k < 8 && !f; k++) { int id = (int) (p >>> (k << 3)) & 0xFF; f = id < glow.length && glow[id] > 0; }
	            } else { int id = v & 0xFF; f = id < glow.length && glow[id] > 0; }
	        }
	    }
	    glowFlag = f; glowVer = ver;
	    return f;
	}
}

final class Memo {
    private static final long K1 = 0x9E3779B97F4A7C15L;
    private static final long K2 = 0xC2B2AE3D27D4EB4FL;
    private static final long K3 = 0x165667B19E3779F9L;
    private static final long K4 = 0x27D4EB2F165667C5L;

    private static final long REFRESH_INTERVAL_NS = 500_000_000L;

    final long[] t;
    final int mask;

    private int sweepCursor;
    private long nextSweepAt;
    private boolean clearRequested;
    private boolean sweeping;

    Memo(int size) {
        if (size < 1 || (size & (size - 1)) != 0) {
            throw new IllegalArgumentException(
                "Memo size must be a power of two"
            );
        }
        t = new long[size];
        mask = size - 1;
    }

    static long hash(long a, long b, long c, long d) {
        long h = a * K1;
        h = (h ^ (h >>> 29)) + b * K2;
        h = (h ^ (h >>> 29)) + c * K3;
        h = (h ^ (h >>> 29)) + d * K4;
        h ^= h >>> 32;
        h *= 0xD6E8FEB86659FD93L;
        h ^= h >>> 32;
        return h | 0x100L;
    }

    /**
     * Request a refresh. Multiple requests are coalesced.
     * This does not clear the cache immediately.
     */
    void requestClear() {
        if (!sweeping) {
            clearRequested = true;
        }
    }

    /**
     * Clears a small batch at most once every 500 ms.
     * A full refresh takes approximately 16 seconds.
     */
    private void maintain() {
        long now = System.nanoTime();

        if (clearRequested && !sweeping) {
            clearRequested = false;
            sweeping = true;
            sweepCursor = 0;
            nextSweepAt = now;
        }

        if (!sweeping || now < nextSweepAt) {
            return;
        }

        int batch = Math.max(1, t.length / 32);
        int end = Math.min(t.length, sweepCursor + batch);

        Arrays.fill(t, sweepCursor, end, 0L);
        sweepCursor = end;
        nextSweepAt = now + REFRESH_INTERVAL_NS;

        if (sweepCursor >= t.length) {
            sweeping = false;
            sweepCursor = 0;
        }
    }

    /** Payload 0..255, or -1 on a miss. */
    int get(long h) {
        maintain();
        long e = t[(int) (h >>> 20) & mask];
        return ((e ^ h) & ~0xFFL) == 0 ? (int) (e & 0xFF) : -1;
    }

    void put(long h, int v) {
        maintain();
        t[(int) (h >>> 20) & mask] = (h & ~0xFFL) | (v & 0xFFL);
    }

    /** Immediate clear for explicit hard resets only. */
    void clear() {
        Arrays.fill(t, 0L);
        sweepCursor = 0;
        clearRequested = false;
        sweeping = false;
        nextSweepAt = 0L;
    }
}


final class SplitDecimal implements Comparable<SplitDecimal> {
    private static final double SPLITTER = 134217729.0;
    private long integerPart;
    private double fractionalPart;

    public SplitDecimal() { }

    public SplitDecimal(double value) {
        if (Double.isNaN(value) || Double.isInfinite(value)) {
            throw new IllegalArgumentException("Cannot split NaN or Infinite values.");
        }
        if (Math.abs(value) >= Long.MAX_VALUE) {
            throw new IllegalArgumentException("Value does not fit the long integer part.");
        }
        setValue(value);
    }

    public SplitDecimal(long integerPart, double fractionalPart) {
        if (Double.isNaN(fractionalPart) || Double.isInfinite(fractionalPart)) {
            throw new IllegalArgumentException("Cannot use NaN or Infinite fractional part.");
        }
        assign(integerPart, fractionalPart);
    }

    /* =================================================================
     * MUTATORS
     * ================================================================= */

    /** Sets this to {@code value}. Exact (truncation + subtraction of an integer is lossless). */
    public void setValue(double value) {
        long i = (long) value;
        this.integerPart = i;
        this.fractionalPart = value - i;
    }

    /** Sets this to {@code integerPart + fractionalPart}, normalizing any overflow / sign conflict. */
    public void setValues(long integerPart, double fractionalPart) {
        assign(integerPart, fractionalPart);
    }

    public void set(SplitDecimal other) {
        this.integerPart = other.integerPart;
        this.fractionalPart = other.fractionalPart;
    }

    public long getIntegerPart() { return integerPart; }
    public double getFractionalPart() { return fractionalPart; }
    public double toDouble() { return integerPart + fractionalPart; }

    /* =================================================================
     * NORMALIZATION
     * ================================================================= */

    /** General normalization: f may be any finite double. */
    private void assign(long i, double f) {
        if (f >= 1.0 || f <= -1.0) {
            long extra = (long) f;      // truncates toward zero, so |f - extra| < 1
            i += extra;
            f -= extra;
        }
        settle(i, f);
    }

    /** Precondition: |f| < 1. Only fixes a sign conflict between i and f, then stores. */
    private void settle(long i, double f) {
        if (i > 0L) {
            if (f < 0.0) {
                f += 1.0;
                i--;
                if (f >= 1.0) { f = 0.0; i++; }   // f was so tiny that f + 1.0 rounded up to 1.0
            }
        } else if (i < 0L) {
            if (f > 0.0) {
                f -= 1.0;
                i++;
                if (f <= -1.0) { f = 0.0; i--; }  // same rounding corner, mirrored
            }
        }
        this.integerPart = i;
        this.fractionalPart = f;
    }

    /* =================================================================
     * ARITHMETIC (zero allocation; all inputs are read into locals before the write,
     * so destination may alias this or other)
     * ================================================================= */

    public SplitDecimal add(SplitDecimal other, SplitDecimal destination) {
        long i = this.integerPart + other.integerPart;
        final double x = this.fractionalPart, y = other.fractionalPart;
        double f = x + y;
        if (f >= 1.0)       { f = (x >= y) ? (x - 1.0) + y : (y - 1.0) + x; i++; }
        else if (f <= -1.0) { f = (x <= y) ? (x + 1.0) + y : (y + 1.0) + x; i--; }
        destination.settle(i, f);
        return destination;
    }

    public SplitDecimal subtract(SplitDecimal other, SplitDecimal destination) {
        long i = this.integerPart - other.integerPart;
        final double x = this.fractionalPart, y = -other.fractionalPart;
        double f = x + y;
        if (f >= 1.0)       { f = (x >= y) ? (x - 1.0) + y : (y - 1.0) + x; i++; }
        else if (f <= -1.0) { f = (x <= y) ? (x + 1.0) + y : (y + 1.0) + x; i--; }
        destination.settle(i, f);
        return destination;
    }

    public SplitDecimal multiply(SplitDecimal other, SplitDecimal destination) {
        final long i1 = this.integerPart, i2 = other.integerPart;
        final double d1 = this.fractionalPart, d2 = other.fractionalPart;
        final double a = (double) i1, b = (double) i2;

        // Split the fractions once.
        double c = SPLITTER * d2;  final double dh = c - (c - d2), dl = d2 - dh;
        c = SPLITTER * d1;         final double eh = c - (c - d1), el = d1 - eh;

        // p1 + e1 == a * d2 exactly. If |a| < 2^26 it is already half-width: no split needed.
        final double p1 = a * d2;
        final double e1;
        if (i1 < (1L << 26) && i1 > -(1L << 26)) {
            e1 = (a * dh - p1) + a * dl;
        } else {
            c = SPLITTER * a;
            final double ah = c - (c - a), al = a - ah;
            e1 = ((ah * dh - p1) + ah * dl + al * dh) + al * dl;
        }

        // p2 + e2 == b * d1 exactly.
        final double p2 = b * d1;
        final double e2;
        if (i2 < (1L << 26) && i2 > -(1L << 26)) {
            e2 = (b * eh - p2) + b * el;
        } else {
            c = SPLITTER * b;
            final double bh = c - (c - b), bl = b - bh;
            e2 = ((bh * eh - p2) + bh * el + bl * eh) + bl * el;
        }

        final double p3 = d1 * d2;

        // Peel integers off first (exact), then sum the fractions with error capture.
        final long n1 = (long) p1, n2 = (long) p2;
        final double x = p1 - n1, y = p2 - n2;
        final double s = x + y;  double bv = s - x;                    // TwoSum
        final double t1 = (x - (s - bv)) + (y - bv);
        final double u = s + p3; bv = u - s;                           // TwoSum
        final double t2 = (s - (u - bv)) + (p3 - bv);
        final long n3 = (long) u;                                      // |u| < 3
        final double v = u - n3;
        final double f = v + ((t1 + t2) + (e1 + e2));
        destination.assign(i1 * i2 + n1 + n2 + n3, f);
        return destination;
    }

    public SplitDecimal divide(SplitDecimal other, SplitDecimal destination) {
        final long oi = other.integerPart;
        final double of = other.fractionalPart;
        if (oi == 0L && of == 0.0) {
            throw new ArithmeticException("Division by zero.");
        }

        final long ai = this.integerPart;
        final double af = this.fractionalPart;
        final double bd = oi + of;
        final double q1 = (ai + af) / bd;
        if (Math.abs(q1) < 1.0) {
            destination.setValue(q1);
            return destination;
        }

        // Reuse the caller's output as scratch when it cannot overwrite either input.
        // This avoids a temporary SplitDecimal allocation in the common non-aliasing case.
        final SplitDecimal t;
        if (destination != this && destination != other) {
            t = destination;
        } else {
            t = new SplitDecimal();
        }
        t.setValue(q1);
        t.multiply(other, t);                    // t = q1 * b
        // The dividend remains intact: when destination aliases it, t is the
        // separate fallback object; otherwise t may alias destination but not this.
        this.subtract(t, t);
        final double q2 = t.toDouble() / bd;
        final long qi = (long) q1;
        destination.assign(qi, (q1 - qi) + q2);
        return destination;
    }

    public SplitDecimal negate(SplitDecimal destination) {
        destination.integerPart = -this.integerPart;
        destination.fractionalPart = -this.fractionalPart;
        return destination;
    }

    /* =================================================================
     * CONVENIENCE WRAPPERS (allocate one result object)
     * ================================================================= */

    public SplitDecimal add(SplitDecimal other)      { return add(other, new SplitDecimal()); }
    public SplitDecimal subtract(SplitDecimal other) { return subtract(other, new SplitDecimal()); }
    public SplitDecimal multiply(SplitDecimal other) { return multiply(other, new SplitDecimal()); }
    public SplitDecimal divide(SplitDecimal other)   { return divide(other, new SplitDecimal()); }
    public SplitDecimal negate()                     { return negate(new SplitDecimal()); }

    /* =================================================================
     * OBJECT CONTRACT
     * ================================================================= */

    /** Canonical form makes lexicographic comparison correct. */
    @Override
    public int compareTo(SplitDecimal o) {
        if (integerPart != o.integerPart) return integerPart < o.integerPart ? -1 : 1;
        if (fractionalPart < o.fractionalPart) return -1;
        if (fractionalPart > o.fractionalPart) return 1;
        return 0;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof SplitDecimal)) return false;
        SplitDecimal that = (SplitDecimal) o;
        return integerPart == that.integerPart && fractionalPart == that.fractionalPart; // -0.0 == 0.0
    }

    @Override
    public int hashCode() {
        // No varargs array / boxing (Objects.hash allocates). -0.0 and 0.0 must hash alike.
        int h = Long.hashCode(integerPart);
        return 31 * h + (fractionalPart == 0.0 ? 0 : Double.hashCode(fractionalPart));
    }

    @Override
    public String toString() {
        if (fractionalPart == 0.0) return Long.toString(integerPart);
        String frac = BigDecimal.valueOf(Math.abs(fractionalPart)).stripTrailingZeros().toPlainString(); // "0.xxx"
        StringBuilder sb = new StringBuilder(frac.length() + 20);
        if (integerPart == 0L && fractionalPart < 0.0) sb.append('-');   // "-0" has no long representation
        sb.append(integerPart).append(frac, 1, frac.length());           // frac.substring(1) == ".xxx"
        return sb.toString();
    }

    public static String fmt3(SplitDecimal value, boolean negate) {
        final long i = value.integerPart;
        final double f = value.fractionalPart;
        final boolean negative = (i < 0 || (i == 0 && f < 0.0)) ^ negate;
        final String digits = Long.toString(i);
        final int start = digits.charAt(0) == '-' ? 1 : 0;
        final int integerLength = digits.length() - start;
        final int milli = (int) (Math.abs(f) * 1000.0);

        // The HUD calls this frequently; build the final string directly instead of
        // allocating substring/fraction strings on every coordinate update.
        if (i == 0L && milli == 0) return "0";
        StringBuilder result = new StringBuilder(integerLength + 8);
        if (negative) result.append('-');

        // Scientific notation for integer magnitudes with 11 or more digits.
        if (integerLength > 10) {
            result.append(digits.charAt(start));
            int end = digits.length();
            while (end > start + 1 && digits.charAt(end - 1) == '0') end--;
            if (end > start + 1) {
                result.append('.');
                result.append(digits, start + 1, end);
            }
            result.append('E').append(integerLength - 1);
            return result.toString();
        }

        result.append(digits, start, digits.length());
        if (milli != 0) {
            result.append('.');
            if (milli < 100) result.append('0');
            if (milli < 10) result.append('0');
            result.append(milli);
            while (result.charAt(result.length() - 1) == '0') result.setLength(result.length() - 1);
        }
        return result.toString();
    }

    public static String format(long value, boolean negate) {
    	if (negate) {
    		if (value == Long.MIN_VALUE) {
    			return "9223372036854775808";
    		}
    		value = -value;
    	}
    	return Long.toString(value);
    }
}
