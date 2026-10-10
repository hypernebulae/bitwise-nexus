package bitwise;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.io.*;
import java.nio.file.*;
import java.text.DecimalFormat;
import java.util.*;
import java.util.List;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;
import java.util.concurrent.locks.LockSupport;
import java.util.zip.*;

import javax.sound.sampled.*;
import javax.swing.*;

import static bitwise.Nexus.*;

@SuppressWarnings("serial")
public class Nexus extends JPanel implements KeyListener, MouseListener, MouseMotionListener, FocusListener, MouseWheelListener {
	static double x, y, z, velX, velY, velZ, yaw, pitch, zoom = 90, sinYaw, sinPitch, cosYaw, cosPitch, amp = 1, flight = 0.1, sensitivity = Math.PI / 1800;
	volatile static boolean vSync = true, caves = true, terrain3D = true, degrees, lock, focus, inside, update = true, sprint, fly, fill, display = true, classic = true, xor, zoomSwitch, sprintRequest, showFPS = true, showXYZ = true, showRot = true, showCyan = true, showMagenta = true, showExtra = true;
	public static byte scale = 1, detail = 1, option, heldBlock, reach = 5, power = 3;
	final static int SIZE = 64, SHIFT = 6, MASK = 63, VOL = SIZE * SIZE * SIZE, BLOCK_COUNT = 32, TEX_STRIDE = 16 * 16 * 3;
	public static short dist = 144, radius = 3;
	static int width = 856, height = 480, resX = 1, resY = 1;
	final static int THREADS = Runtime.getRuntime().availableProcessors();
	volatile static long focusTime, hoveredX = -1, hoveredY = -1, hoveredZ = -1, newHoverX = -1, newHoverY = -1, newHoverZ = -1;
	volatile static int dirX, dirY, dirZ, newDirX, newDirY, newDirZ;
	static long activity = System.currentTimeMillis(), time, fps, frames, x0 = -1, y0 = -1, z0 = -1, x1 = -1, y1 = -1, z1 = -1, fpsTime = System.currentTimeMillis();
	final static byte texRes = 16, AXIS_X = 0, AXIS_Y = 1, AXIS_Z = 2, CROSS = 32, perlinRes = 127;
	final static int MAGIC = 0x4E585335; // save format id ("NXS5")
	static final double[] PERLIN = new double[perlinRes + 1];
	static volatile byte[] hotbar = new byte[]{};
	public static String VERSION = "Bitwise Nexus 2.1";
	volatile static String hoveredType;
	static Vec3 light = new Vec3(0), sunColor = new Vec3(0), ambColor = new Vec3(0), skyColor = new Vec3(0);
	static final Vec3 SUN_LOW = new Vec3(1, 0.5, 0), SUN_DAY = new Vec3(1), SUN_NIGHT = new Vec3(0.3, 0.3, 0.5);
	static final Vec3 AMB_LOW = new Vec3(0.6, 0.5, 0.5), AMB_DAY = new Vec3(0.5), AMB_NIGHT = new Vec3(0.3, 0.3, 0.5);
	static final Vec3 SKY_LOW = Vec3.rgb(0x463C53), SKY_DAY = Vec3.rgb(0x51BAF7), SKY_NIGHT = new Vec3(0);
	static JFrame frame;
	static boolean fullscreen;
	static int windowedWidth = width, windowedHeight = height;
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
	static BufferedImage atlasImg = new BufferedImage(texRes, BLOCK_COUNT * 3 * texRes, 2);
	static int[] atlas = ((DataBufferInt) atlasImg.getRaster().getDataBuffer()).getData();
	static final long TICK_NS = 10_000_000L;
	static final double TELEPORT = 1.0;
	static double prevX, prevY, prevZ, viewX, viewY, viewZ, renderAlpha;
	static World world = new World(radius);
	static final List<Render> workers = new ArrayList<>();
	static long lcx = Long.MIN_VALUE, lcy, lcz;
	static volatile boolean chunkDirty = true, needGround = true;
	static final DecimalFormat FMT3 = new DecimalFormat("0.###"), FMT1 = new DecimalFormat("0.#\u00B0");
	static Font guiFont;
	static int guiFontScale = -1;
	final static ExecutorService pool = Executors.newFixedThreadPool(THREADS, r -> {
		Thread t = new Thread(r, "nexus-worker");
		t.setDaemon(true);
		return t;
	});
	static final int AUTO_GUI_SCALE_WIDTH = 2000;
	static final double AUTO_ZOOM_MIN = 5;
	static final double AUTO_ZOOM_MAX = 1000;
	static final int AUTO_ZOOM_BASE_WIDTH = 856;
	static final int AUTO_ZOOM_REFERENCE_WIDTH = 2880;
	static final double AUTO_ZOOM_BASE = 90;
	static final double AUTO_ZOOM_REFERENCE = 250;
	static final Map<Long, Long> chunkLastSeen = new HashMap<>();
	static long lastChunkCleanup;
	static double red = 0.3, green = 0.4, blue = 0.5;
	static volatile boolean toggleFullscreenRequested;
	static final Map<Long, byte[]> savedChunks = new HashMap<>();
	static final byte[] EMPTY = new byte[0];
	static final String[] NAMES = new String[BLOCK_COUNT];
	static final Color HOTBAR_BG = new Color(0x33, 0x33, 0x33, 0x7F).darker(), HOTBAR_BORDER = Color.gray.darker();
	static int page;
	volatile static boolean particlesOn = true;
	static boolean titleIdle;
	static int zoomWidth = -1;
	static final int MAX_LOAD_PER_PASS = 64;
	final static byte AIR = 0, GRASS = 1, DIRT = 2, STONE = 3, BRICKS = 4, WOOD = 5, LEAVES = 6, GLASS = 7, SLATE = 8, DYNAMITE = 9, SNOW = 10, MAGMA = 11, SAND = 12, ICE = 13, TOPAZ = 14, EMERALD = 15, RUBY = 16, SAPPHIRE = 17, AMETHYST = 18, COPPER = 19, IRON_ORE = 20, COPPER_ORE = 21, COAL_ORE = 22, OBSIDIAN = 23, CLAY = 24, GRAVEL = 25, PLANKS = 26, IRON = 27, COAL = 28, ASH = 29, TILE = 30, MOSS = 31;
	static volatile int lightQ = 2;   // 0 basic, 1 AO + glow, 2 AO + skylight + lantern
	static final String[] LIGHT_NAMES = { "Basic", "AO + Glow", "AO + Skylight + Lantern" };
	static double caveMix;            // 0 = outside, 1 = deep underground (smoothed)
	static final float[] GLOW = glow();

	static final byte[][] PAGES = {
		{ GRASS, DIRT, STONE, BRICKS, WOOD, LEAVES, GLASS, SLATE },
		{ DYNAMITE, MAGMA, TOPAZ, EMERALD, ICE, SNOW, SAND, ASH },
		{ COAL_ORE, COPPER_ORE, IRON_ORE, COAL, COPPER, IRON, PLANKS, OBSIDIAN },
		{ CLAY, GRAVEL, RUBY, SAPPHIRE, AMETHYST, MOSS, TILE, AIR } };
	static final byte[] XOR_PAGE = { BRICKS, DIRT, GRASS, WOOD, STONE, LEAVES, GLASS, SLATE };

	//  							RUBY      SAPPH     AMETH     COPPER    IRON ORE  COP_ORE   COAL ORE  OBSIDIAN
	static final int[] X_BASE   = { 0xD4123A, 0x1F4FE0, 0x9B3CD8, 0xDE774B, 0x7F7F7F, 0x7F7F7F, 0x7F7F7F, 0x1E1A2D,
	//  							CLAY      GRAVEL    PLANKS    IRON      COAL      ASH       TILE      MOSS
								  0xB4704F, 0x8C8C96, 0xD6BA90, 0xEBCBAE, 0x303030, 0x5A5A5A, 0xFFFFFF, 0x5A8F3C };
	//								RUBY      SAPPH     AMETH     COPPER    IRON ORE  COP_ORE   COAL ORE  OBSIDIAN
	static final int[] X_ACCENT = { 0xFF9AB0, 0x9CC4FF, 0xE0B0FF, 0xF7A986, 0xE0B890, 0xC87850, 0x202020, 0x5A3C8C,
	//								CLAY      GRAVEL    PLANKS    IRON      COAL      ASH       TILE      MOSS
								 0xC88B6A, 0x5A5A64, 0xC29759, 0xF5E7DA, 0x505050, 0x5A5A5A, 0x2A2A2A, 0x8CC858 };
	static final int[] X_STYLE  = { 4, 4, 4, 3, 1, 1, 1, 1, 0, 1, 2, 3, 1, 0, 5, 1 };

	static {
		Random r = new Random(0);
		for (int i = 0; i < perlinRes; i++) {
			PERLIN[i] = r.nextDouble();
		}
		for (int cx = 0; cx < CROSS; cx++) {
			for (int cy = 0; cy < CROSS; cy++) {
				int ax = Math.abs(cx - CROSS / 2) + 2, ay = Math.abs(cy - CROSS / 2) + 2;
				if (ax * ay < Math.sqrt(CROSS * CROSS / 2) && ax + ay < CROSS * 0.4375 && ax + ay > CROSS * 0.296875)
					crosshair.setRGB(cx, cy, 0xFFFFFFFF);
			}
		}
		for (int i = 0; i < THREADS; i++)
			workers.add(new Render());
		NAMES[AIR] = "Air";       NAMES[GRASS] = "Grass";   NAMES[DIRT] = "Dirt";
		NAMES[STONE] = "Stone";   NAMES[BRICKS] = "Bricks"; NAMES[WOOD] = "Wood";
		NAMES[LEAVES] = "Leaves"; NAMES[GLASS] = "Glass";   NAMES[SLATE] = "Slate";
		NAMES[DYNAMITE] = "Dynamite"; NAMES[SNOW] = "Snow"; NAMES[MAGMA] = "Magma";
		NAMES[SAND] = "Sand";     NAMES[ICE] = "Ice";       NAMES[TOPAZ] = "Topaz";
		NAMES[EMERALD] = "Emerald"; NAMES[RUBY] = "Ruby"; NAMES[SAPPHIRE] = "Sapphire"; NAMES[AMETHYST] = "Amethyst"; NAMES[COPPER] = "Copper";
		NAMES[IRON_ORE] = "Iron Ore"; NAMES[COPPER_ORE] = "Copper Ore"; NAMES[COAL_ORE] = "Coal Ore"; NAMES[OBSIDIAN] = "Obsidian";
		NAMES[CLAY] = "Clay"; NAMES[GRAVEL] = "Gravel"; NAMES[PLANKS] = "Planks"; NAMES[IRON] = "Iron";
		NAMES[COAL] = "Coal"; NAMES[ASH] = "Ash"; NAMES[TILE] = "Tile"; NAMES[MOSS] = "Moss";
	}

	public static void main(String[] args) {
		frame = new JFrame(VERSION);
		Nexus nexus = new Nexus();
		frame.setSize(width, height);
		frame.setDefaultCloseOperation(3);
		frame.setLocationRelativeTo(null);
		hidden = frame.getToolkit().createCustomCursor(new BufferedImage(1, 1, 2), new Point(), null);
		frame.setCursor(hidden);
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

	/** Light a block emits on its own (added on top of normal lighting). */
	static float[] glow() {
		float[] a = new float[BLOCK_COUNT];
		a[MAGMA] = 0.9f; a[RUBY] = 0.3f; a[AMETHYST] = 0.3f; a[SAPPHIRE] = 0.25f;
		a[TOPAZ] = 0.25f; a[EMERALD] = 0.2f;
		return a;
	}

	/** 0 at night, 1 at midday (smooth). */
	static double daylight() {
		return smoothstep(-0.2, 0.35, -light.y);
	}

	private static long caveCheckX = Long.MIN_VALUE, caveCheckY, caveCheckZ;
	private static double caveTarget;

	/** Smoothly tracks cave cover using an unbounded-to-world-top vertical ray.
	 * The ray passes through air until it reaches the roof; only the continuous
	 * opaque roof thickness counts, so tall caves are not limited to 64 blocks. */
	static void updateCaveMix() {
		long bx = (long) Math.floor(viewX), by = (long) Math.floor(viewY), bz = (long) Math.floor(viewZ);
		if (by < 0) { caveMix *= 0.96; return; }
		if (bx != caveCheckX || by != caveCheckY || bz != caveCheckZ) {
			caveCheckX = bx; caveCheckY = by; caveCheckZ = bz;
			int roofBlocks = 0;
			boolean hitRoof = false;
			for (long yy = by - 1; yy >= 0; yy--) {
				byte b = getBlock(bx, yy, bz);
				if (b == AIR || b == LEAVES || b == GLASS) {
					if (hitRoof) break;
					continue;
				}
				hitRoof = true;
				roofBlocks++;
			}
			int coveredNeighbours = 0;
			if (roofBlocks >= 20) {
				for (int dx = -1; dx <= 1; dx++) for (int dz = -1; dz <= 1; dz++) {
					if (dx == 0 && dz == 0) continue;
					int column = 0;
					boolean hit = false;
					for (long yy = by - 1; yy >= 0; yy--) {
						byte b = getBlock(bx + dx, yy, bz + dz);
						if (b == AIR || b == LEAVES || b == GLASS) {
							if (hit) break;
							continue;
						}
						hit = true;
						column++;
					}
					if (column >= 20) coveredNeighbours++;
				}
			}
			caveTarget = roofBlocks >= 20 && coveredNeighbours >= 3 ? 1 : 0;
		}
		caveMix += (caveTarget - caveMix) * 0.04;
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

	private static void savePrev() {
		prevX = x;
		prevY = y;
		prevZ = z;
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

	private static double blend(double from, double to) {
		if (Math.abs(to - from) > TELEPORT) // respawn, load, dialog: don't slide across the map
			return to;
		return from + (to - from) * renderAlpha;
	}

	private static void updateView() {
		viewX = blend(prevX, x);
		viewY = blend(prevY, y);
		viewZ = blend(prevZ, z);
	}

	private static int cachedRate = 60;
	private static long rateStamp;

	private static int getRefreshRate() {
		long n = System.currentTimeMillis();
		if (n - rateStamp > 2000) {
			rateStamp = n;
			int rate = GraphicsEnvironment.getLocalGraphicsEnvironment().getDefaultScreenDevice().getDisplayMode().getRefreshRate();
			cachedRate = rate > 0 && rate < 1000 ? rate : 60;
		}
		return cachedRate;
	}

	private static void limitFrame(long frameStartNs) {
	    if (!vSync) {
	        return;
	    }

	    long frameDurationNs = 1_000_000_000L / getRefreshRate();
	    long deadline = frameStartNs + frameDurationNs;

	    while (true) {
	        long remaining = deadline - System.nanoTime();

	        if (remaining <= 0) {
	            break;
	        }

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

	static void stash(long key, byte[] data) {
		savedChunks.put(key, data == null ? EMPTY : encode(data));
	}

	/** Persist (if edited) and unload one ring slot. */
	static void unloadSlot(int s) {
		long k = world.keys[s];
		if (k == World.NONE)
			return;
		if (world.dirty[s])
			stash(k, world.data[s]);
		world.keys[s] = World.NONE;
		world.data[s] = null;
		world.dirty[s] = false;
	}

	/** Copy every edited live chunk into savedChunks (before clear/resize/save). */
	static void flushDirty() {
		for (int s = 0; s < world.keys.length; s++)
			if (world.keys[s] != World.NONE && world.dirty[s]) {
				stash(world.keys[s], world.data[s]);
				world.dirty[s] = false;
			}
	}

	static int autoGuiScale(int windowWidth) {
		return windowWidth > AUTO_GUI_SCALE_WIDTH ? 2 : 1;
	}

	static double autoZoom(int windowWidth) {
		double t = (windowWidth - AUTO_ZOOM_BASE_WIDTH) / (double) (AUTO_ZOOM_REFERENCE_WIDTH - AUTO_ZOOM_BASE_WIDTH);
		double value = AUTO_ZOOM_BASE + (AUTO_ZOOM_REFERENCE - AUTO_ZOOM_BASE) * t;
		value = Math.round(value / 5.0) * 5.0;
		return Math.max(AUTO_ZOOM_MIN, Math.min(AUTO_ZOOM_MAX, value));
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

	static void setDist(int d) {
		dist = (short) Math.max(16, Math.min(1024, d));
		short r = (short) ((dist + SIZE - 1) / SIZE);
		if (r != radius) {
			flushDirty();
			radius = r;
			world.resize(r);
			chunkLastSeen.clear();
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
		case GRASS: case LEAVES: case MOSS: return 2;
		case WOOD: case PLANKS: case DYNAMITE: return 3;
		case ICE: case TOPAZ: case EMERALD: case RUBY: case SAPPHIRE: case AMETHYST: return 4;
		case SAND: case ASH: return 5;
		case IRON: case COPPER: return 6;
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
		Thread t = new Thread(Nexus::mixer, "nexus-audio");
		t.setDaemon(true);
		t.start();
		Thread music = new Thread(Nexus::musicLoop, "nexus-bytebeat");
		music.setDaemon(true);
		music.start();
	}

	static final int BB_MAX_SECONDS = 60;
	static final String[][] BYTEBEAT = {
		{ "Useless1", "Decent-Manager-6169", "35280" },
		{ "e", "absolute197", "46000" },
		{ "qai", "lhphr", "44100" },
		{ "ÐiskΩtroÑ", "lhphr", "9930" },
		{ "Steady On Tim, It's Only A Budget Game", "Gasman", "44100" },
		{ "Crystal Cave", "kOLbOSa_exe", "8000" },
		{ "cave_7", "Chasyxx", "31000" }
	};

	static final class MusicVoice {
		final float[] samples;
		final int rate, loopSamples, fadeIn, fadeOut, extraLoop;
		long position; // output-rate frames
		MusicVoice(float[] samples, int loopSamples, int rate) {
			this.samples = samples; this.loopSamples = loopSamples; this.rate = rate;
			this.fadeIn = rate / 2;
			this.extraLoop = rate * 3;
			this.fadeOut = rate * 2;
		}
		boolean finished() { return position * (long) rate / RATE >= (long) loopSamples + extraLoop; }
	}

	static void musicLoop() {
		int index = 0;
		try { Thread.sleep(30000); } catch (InterruptedException e) { Thread.currentThread().interrupt(); return; }
		while (true) {
			try {
				if (!sound) { Thread.sleep(1000); continue; }
				String[] track = BYTEBEAT[index];
				int rate = Integer.parseInt(track[2]);
				float[] samples = renderBytebeat(track, rate);
				musicVoice = new MusicVoice(samples, samples.length, rate);
				say("Now playing: " + track[0] + " by " + track[1]);
				while (musicVoice != null && !musicVoice.finished()) Thread.sleep(100);
				musicVoice = null;
				Thread.sleep(20000);
				index = (index + 1) % BYTEBEAT.length;
			} catch (Throwable e) {
				System.err.println("Bytebeat player error: " + e);
				e.printStackTrace();
				musicVoice = null;
				try { Thread.sleep(5000); } catch (InterruptedException ignored) { Thread.currentThread().interrupt(); return; }
				index = (index + 1) % BYTEBEAT.length;
			}
		}
	}

	static float[] renderBytebeat(String[] track, int rate) throws Exception {
		return renderBytebeatJava(track[0], rate * BB_MAX_SECONDS, rate);
	}

	static float[] renderBytebeatJava(String name, int count, int rate) {
		float[] out = new float[count];
		double[] rev = new double[12288]; int rp = 0; double[] delay = new double[120000];
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
			} else if ("cave_7".equals(name)) {
			double tt=t/4.0; int ti=(int)tt; int c=8*((int)(5*tt/(4+(ti>>15)%16)*(1+(3&ti>>13)))>>(1&ti>>12)&16);
				int ix=Math.floorMod((int)(tt*4),delay.length); double d=1.5*((c* Math.pow(1.00009,-(long)tt%16384))%256/4.0+delay[ix]*.8); delay[ix]=64;
			v=Double.isNaN(d)?128:d;
			}
			out[i]=normalizeBytebeat(v);
		}
		return out;
	}

	// Fast Java equivalent of x=t=>(1.22*t*1.0596**parseInt(...,36)&128)*(-t>>8&31)/16.
	// The source selects one of eight fixed characters; cache their base-36 powers instead of
	// parsing strings and exponentiating on every sample.
	static final double[] E_PITCH = { Math.pow(1.0596, 17), Math.pow(1.0596, 0),
		Math.pow(1.0596, 12), Math.pow(1.0596, 10), Math.pow(1.0596, 17),
		Math.pow(1.0596, 1), Math.pow(1.0596, 13), Math.pow(1.0596, 12) };

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

	static float normalizeBytebeat(double value) {
		if (Double.isNaN(value) || Double.isInfinite(value)) value = 128;
		value %= 256; if (value < 0) value += 256;
		return (float) ((value - 128) / 128.0);
	}

	static int findLoop(float[] s, int rate) {
		int window = Math.max(64, rate / 100), min = rate * 2, max = Math.min(s.length - window, rate * 30);
		if (max <= min) return s.length;
		// Compare short windows at regular intervals; use a looser threshold for noisy bytebeat.
		for (int p = min; p < max; p += Math.max(8, rate / 1000)) {
			double err = 0;
			for (int j = 0; j < window; j++) err += Math.abs(s[j] - s[p + j]);
			if (err / window < 0.025) return p;
		}
		return s.length;
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
				if (mv != null && sound) {
					for (int i = 0; i < 512; i++) {
						long p = mv.position;
						double sourcePos = p * (double) mv.rate / RATE;
						long phase = (long) Math.floor(sourcePos);
						long local = phase < mv.loopSamples ? phase : phase % mv.loopSamples;
						int at = (int) Math.min(mv.loopSamples - 1L, local);
						int next = at + 1 < mv.loopSamples ? at + 1 : 0;
						double frac = sourcePos - Math.floor(sourcePos);
						float sample = (float) (mv.samples[at] * (1 - frac) + mv.samples[next] * frac);
						long end = (long) mv.loopSamples + mv.extraLoop;
						double musicPos = p * (double) mv.rate / RATE;
						double gain = Math.min(1, musicPos / mv.fadeIn);
						if (musicPos >= end - mv.fadeOut) gain *= Math.max(0, (end - musicPos) / (double) mv.fadeOut);
						mix[i] += sample * (float) (gain * 0.40);
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
		if (!sound || vol < 0.01)
			return;
		synchronized (voices) {
			if (voices.size() < 24)
				voices.add(new Voice(s, (float) vol));
		}
	}

	private static double dist(double bx, double by, double bz) {
		double dx = bx + .5 - x, dy = by + .5 - y, dz = bz + .5 - z;
		return Math.sqrt(dx * dx + dy * dy + dz * dz);
	}

	/** action: 0 break, 1 place, 2 step */
	static void block(byte id, int action, double bx, double by, double bz) {
		if (id == AIR)
			return;
		play(bank[(kind(id) * 3 + action) * VAR + RND.nextInt(VAR)], 2 * VOLUME[action] * 0.5 / (1 + dist(bx, by, bz) * 0.1));
	}

	static void boom(double bx, double by, double bz) {
		play(boom, 2 / (1 + dist(bx, by, bz) * 0.05));
	}

	/** Called every tick; plays a footstep every ~1.8 blocks walked on the ground. */
	static void step(byte below, double moved) {
		if (below == AIR)
			return;
		walked += moved;
		if (walked > 1.8) {
			walked = 0;
			block(below, 2, x, y + 1.5, z);
		}
	}

	// ------------------------------------------------------------------ main loop

	private void run() {
		try {
			spawn();
			center();
			textures();
			init();
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
				boolean idle = System.currentTimeMillis() - activity > 15000;
				if (idle != titleIdle) {
					titleIdle = idle;
					final String t = idle ? VERSION + " - Inactive!" : VERSION;
					SwingUtilities.invokeLater(() -> frame.setTitle(t));
				}
				if (idle) {
					try { Thread.sleep(200); } catch (InterruptedException e) { Thread.currentThread().interrupt(); }
				}
				Runnable task;
				while ((task = tasks.poll()) != null)
					task.run();

				if (lock && focus && System.currentTimeMillis() - focusTime >= 200)
					lock = false;

				ensureChunks();
				cleanupOldChunks();
				if (needGround) {
					needGround = false;
					y = groundY(x, z);
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

				newHoverY = -1;
				Render.prepare();
				try {
					pool.invokeAll(workers);
				} catch (InterruptedException e) {
					Thread.currentThread().interrupt();
				}
				Particles.render();
				hoveredX = newHoverX;
				hoveredY = newHoverY;
				hoveredZ = newHoverZ;
				dirX = newDirX;
				dirY = newDirY;
				dirZ = newDirZ;

				swapBuffers();
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

	private static void updateHotbar() {
		byte[] want = xor ? XOR_PAGE : PAGES[page];
		if (hotbar != want)
			hotbar = want;
		if (heldBlock >= want.length || heldBlock < 0)
			heldBlock = 0;
	}

	private static void handleKeys() {
		if (fire(KeyEvent.VK_C, 200))
			classic = !classic;
		if (key(KeyEvent.VK_F1))
			option = 0;
		if (key(KeyEvent.VK_F2))
			option = 1;
		if (key(KeyEvent.VK_F3))
			option = 2;
		if (fire(KeyEvent.VK_F4, 200))
			display = !display;
		if (key(KeyEvent.VK_T))
			yaw = pitch = 0;
		if (fire(KeyEvent.VK_X, 200)) {
			xor = !xor;
			textures();
		}
		if (!xor && fire(KeyEvent.VK_E, 200)) page = (page + 1) % PAGES.length;
		if (!xor && fire(KeyEvent.VK_Q, 200)) page = (page + PAGES.length - 1) % PAGES.length;
		if (fire(KeyEvent.VK_V, 200)) {
			particlesOn = !particlesOn;
			if (!particlesOn) Particles.clear();
		}
		if (fire(KeyEvent.VK_Z, 200))
			zoomSwitch = !zoomSwitch;

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
				if (key(KeyEvent.VK_1 + i)) {
					heldBlock = (byte) i;
					break;
				}
			}
		}

		if (fire(KeyEvent.VK_F6, 200))
		    vSync = !vSync;
		if (fire(KeyEvent.VK_F7, 500))
			fill = true;
		if (fire(KeyEvent.VK_F8, 500)) {
			fill = false;
			boolean all = x0 != -1 && y0 != -1 && z0 != -1 && x1 != -1 && y1 != -1 && z1 != -1;
			if (all) {
				fill(hotbar[heldBlock], Math.min(x0, x1), Math.min(y0, y1), Math.min(z0, z1), Math.max(x0, x1) + 1, Math.max(y0, y1) + 1, Math.max(z0, z1) + 1, true);
			}
			x0 = y0 = z0 = x1 = y1 = z1 = -1;
		}
		if (key(KeyEvent.VK_U)) {
			showFPS = showXYZ = showRot = showCyan = showMagenta = showExtra = true;
		}
		if (fire(KeyEvent.VK_F, 200))
			fly = !fly;
		if (key(KeyEvent.VK_G))
			outline();
		if (fire(KeyEvent.VK_N, 250)) {
			locTarget = (locTarget + 1) % LOC_NAMES.length;
			say("Locate: " + LOC_NAMES[locTarget] + " (B to teleport)");
		}
		if (fire(KeyEvent.VK_B, 500))
			locate(locTarget);
		if (fire(KeyEvent.VK_K, 250)) {
			sound = !sound;
			say("Sound: " + (sound ? "on" : "off"));
		}
		if (fire(KeyEvent.VK_L, 250)) {
			lightQ = (lightQ + 1) % 3;
			say("Lighting: " + LIGHT_NAMES[lightQ]);
		}
	}

	// ------------------------------------------------------------------ physics

	private static void tick(long now) {
		time++;
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

		// Ground effects: evaluated once per tick (was evaluated inside the 12x3 collider loop,
		// compounding the factor ~24-36 times). Exponent 24 keeps roughly the old feel.
		byte below = getBlock((long) Math.floor(x), (long) Math.floor(y + 1.5), (long) Math.floor(z));
		if (below == TOPAZ && velY <= 0)
			velY = -0.2;
		if (below == ICE) {
			velX *= 1.27;
			velZ *= 1.27;
		} else if (below == SAND) {
			velX *= 0.79;
			velZ *= 0.79;
		}

		OUTER: for (int axis = 0; axis < 3; axis++) {
			double newX = x + velX * ((axis + AXIS_Y) % 3 / 2);
			double newY = y + velY * ((axis + AXIS_X) % 3 / 2);
			double newZ = z + velZ * ((axis + AXIS_Z) % 3 / 2);
			for (int collider = 0; collider < 12; collider++) {
				long colliderX = (long) Math.floor(newX + (collider & 1) * 0.6 - 0.3);
				long colliderY = (long) Math.floor(newY + ((collider >> 2) - 1) * 0.8 + 0.65);
				long colliderZ = (long) Math.floor(newZ + (collider >> 1 & 1) * 0.6 - 0.3);
				if (colliderY < 0)
					continue;
				if (getBlock(colliderX, colliderY, colliderZ) != AIR) {
					if (axis != AXIS_Z)
						continue OUTER;
					if (key(KeyEvent.VK_SPACE) && velY > 0) {
						velY = -0.1;
						break OUTER;
					}
					velY = 0;
					break OUTER;
				}
			}
			x = newX;
			y = newY;
			z = newZ;
		}

		// clear any blocks overlapping the player (loaded chunks only, never allocates)
		for (int collider = 0; collider < 12; collider++) {
			long mx = (long) Math.floor(x + (collider & 1) * 0.6 - 0.3);
			long my = (long) Math.floor(y + ((collider >> 2) - 1) * 0.8 + 0.65);
			long mz = (long) Math.floor(z + (collider >> 1 & 1) * 0.6 - 0.3);
			setBlock(mx, my, mz, AIR);
		}

		double moved = Math.hypot(x - prevX, z - prevZ);
		step(fly ? AIR : below, moved);
		Particles.sprintTrail(fly ? AIR : below, moved);
		Particles.update();
	}

	// ------------------------------------------------------------------ world generation

	private static void spawn() {
		Random rand = new Random();
		short spawnX = (short) (rand.nextInt(8192) - 4096);
		short spawnZ = (short) (rand.nextInt(8192) - 4096);
		x = spawnX + 0.5;
		z = spawnZ + 0.5;
		y = groundY(x, z); // estimate; refined from real blocks once the chunks exist
		needGround = true;
		chunkDirty = true;
	}

	/** Player y standing on the first solid block of this column (uses real blocks when loaded, else an estimate). */
	static double groundY(double wx, double wz) {
		long bx = (long) Math.floor(wx), bz = (long) Math.floor(wz);
		for (long yy = 0; yy < 1024; yy++) {
			byte[] c = world.chunk(bx >> SHIFT, yy >> SHIFT, bz >> SHIFT);
			if (c == World.UNLOADED)
				break;
			if (getBlock(bx, yy, bz) != AIR)
				return yy - 1.54;
		}
		return estimateGround(bx, bz);
	}

	static double estimateGround(long bx, long bz) {
		if (terrain3D) {
			double half = 0.5 * TK * Math.abs(amp) * TDIV;
			long lo = (long) Math.floor(TBASE - half) - 1, hi = (long) Math.ceil(TBASE + half) + 1;
			for (long yy = lo; yy <= hi; yy++)
				if (density(bx, yy, bz) > 0)
					return yy - 1.54;
			return TBASE - 1.54;
		}
		return terrainHeight(bx, bz) - 1.54;
	}

	static long terrainHeight(long wx, long wz) {
		return (long) ((Math.round(128 + noise(wx / 128.0, wz / 128.0) * 50) - 1) * amp);
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
			r += (n1 + ry * (n2 - n1)) * amp;
			xi <<= 1;
			xd *= 2;
			yi <<= 1;
			yd *= 2;
			if (xd >= 1) {
				xi++;
				xd--;
			}
			if (yd >= 1) {
				yi++;
				yd--;
			}
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
			double n1 = PERLIN[of % perlinRes];
			double n2 = PERLIN[(of + 1) % perlinRes];
			double n3 = PERLIN[(of + 16) % perlinRes];
			double n4 = PERLIN[(of + 17) % perlinRes];
			n1 += rx * (n2 - n1);
			n3 += rx * (n4 - n3);
			r += (n1 + ry * (n3 - n1)) * a; // proper bilinear (old code overwrote n4 and ignored its first half)
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

	private static void cleanupOldChunks() {
	    long now = System.currentTimeMillis();
	    if (now - lastChunkCleanup < 1000L)
	        return;
	    lastChunkCleanup = now;

	    long cx = chunkOf(x), cy = chunkOf(y), cz = chunkOf(z);
	    int r = radius;
	    int verticalRadius = Math.min(r, 4);
	    long cutoff = now - 10000;

	    Iterator<Map.Entry<Long, Long>> it = chunkLastSeen.entrySet().iterator();
	    while (it.hasNext()) {
	        Map.Entry<Long, Long> entry = it.next();
	        long[] c = World.decodeKey(entry.getKey());
	        long dx = wrap21(c[0] - cx), dy = wrap21(c[1] - cy), dz = wrap21(c[2] - cz);
	        c[0] = cx + dx; c[1] = cy + dy; c[2] = cz + dz;
	        boolean inRange = dy >= -verticalRadius && dy <= verticalRadius && dx * dx + dz * dz <= (long) r * r;
	        if (!inRange && entry.getValue() < cutoff) {
	        	int s = world.slot(c[0], c[1], c[2]);
	        	if (world.keys[s] == entry.getKey())
	        		unloadSlot(s);
	            it.remove();
	        }
	    }
	}

	private static void ensureChunks() {
	    long cx = chunkOf(x);
	    long cy = chunkOf(y);
	    long cz = chunkOf(z);

	    if (!chunkDirty && cx == lcx && cy == lcy && cz == lcz)
	        return;

	    chunkDirty = false;
	    lcx = cx;
	    lcy = cy;
	    lcz = cz;

	    int r = radius;
	    int verticalRadius = Math.min(r, 4);

	    List<long[]> pending = new ArrayList<>();
	    for (int dx = -r; dx <= r; dx++)
	    	for (int dz = -r; dz <= r; dz++) {
	    		if (dx * dx + dz * dz > r * r)
	    			continue;
	    		for (int dy = -verticalRadius; dy <= verticalRadius; dy++)
	    			if (!world.has(cx + dx, cy + dy, cz + dz))
	    				pending.add(new long[] { cx + dx, cy + dy, cz + dz });
	    	}

	    List<long[]> missing = new ArrayList<>();
	    if (!pending.isEmpty()) {
	    	pending.sort(Comparator.comparingLong(p -> {
	    		long a = p[0] - cx, b = p[1] - cy, c = p[2] - cz;
	    		return a * a + b * b + c * c;
	    	}));
	    	int n = Math.min(pending.size(), MAX_LOAD_PER_PASS);
	    	if (pending.size() > n)
	    		chunkDirty = true; // more to load next frame
	    	for (int i = 0; i < n; i++) {
	    		long[] p = pending.get(i);
	    		unloadSlot(world.slot(p[0], p[1], p[2]));
	    		byte[] saved = savedChunks.get(World.key(p[0], p[1], p[2]));
	    		if (saved != null)
	    			world.put(p[0], p[1], p[2], saved.length == 0 ? null : decode(saved));
	    		else
	    			missing.add(p);
	    	}
	    }

	    if (missing.isEmpty())
	        return;

	    final World w = world;

	    List<Callable<Void>> jobs = new ArrayList<>(missing.size());

	    for (long[] m : missing) {
	        jobs.add(() -> {

	            byte[] generated = generate(
	                m[0],
	                m[1],
	                m[2]
	            );

	            w.put(
	                m[0],
	                m[1],
	                m[2],
	                generated
	            );

	            return null;
	        });
	    }

	    try {
	        pool.invokeAll(jobs);
	    } catch (InterruptedException e) {
	        Thread.currentThread().interrupt();
	        return;
	    }

	    for (long[] m : missing) {
	    	features(m[0], m[1], m[2]);
	    	caveFeatures(m[0], m[1], m[2]);
	    	basinFeatures(m[0], m[1], m[2]);
	    }

	    long generatedSeen = System.currentTimeMillis();
	    for (long[] m : missing)
	        chunkLastSeen.put(World.key(m[0], m[1], m[2]), generatedSeen);
	}

	static final double TBASE = 160, TDIV = 24, TK = 10;

	static double density(double wx, double wy, double wz) {
		double large = noise3(
				wx / 800.0,
				0,
				wz / 800.0,
				0x71
		);

		/*
		 * Large regions become plains rather than just individual
		 * flat patches.
		 *
		 * 0 = normal terrain
		 * 1 = strong plains behavior
		 */
		double plains = smoothstep(0.58, 0.82, large);

		double rough =
			  0.50 * noise3(wx / 180.0, wy / 150.0, wz / 180.0, 0x11)
			+ 0.30 * noise3(wx / 64.0,  wy / 56.0,  wz / 64.0,  0x22)
			+ 0.20 * noise3(wx / 24.0,  wy / 28.0,  wz / 24.0,  0x33);

		/*
		 * Plains still have slight rolling variation, but are much
		 * flatter than mountainous regions.
		 */
		double plainTerrain =
				0.5
				+ 0.055 * noise3(
						wx / 300.0,
						wy / 240.0,
						wz / 300.0,
						0x91
				);

		double terrainNoise =
				rough * (1.0 - plains)
				+ plainTerrain * plains;

		return (wy - TBASE) / TDIV + TK * amp * (terrainNoise - 0.5);
	}

	static double smoothstep(double edge0, double edge1, double x) {
		double t = (x - edge0) / (edge1 - edge0);
		t = Math.max(0.0, Math.min(1.0, t));
		return t * t * (3.0 - 2.0 * t);
	}

	private static byte[] generate(long cx, long cy, long cz) {
		byte[] data = terrain3D ? generate3D(cx, cy, cz) : generate2D(cx, cy, cz);
		if (data != null) {
			if (caves) {
				carveCaves(data, cx, cy, cz);
				carveBasins(data, cx, cy, cz);
			}
			placeOres(data, cx, cy, cz);
		}
		return data;
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
			Arrays.fill(g, 1f); // entirely below the lowest possible surface: solid
		} else {
			for (int gz = 0; gz < n; gz++)
				for (int gy = 0; gy < ny; gy++)
					for (int gx = 0; gx < n; gx++)
						g[gz * nyn + gy * n + gx] = (float) density(baseX + gx * CAVE_STEP, baseY - 8 + gy * CAVE_STEP, baseZ + gz * CAVE_STEP);
		}
		byte[] data = null;
		float[] col = GEN_COL.get();
		for (int lz = 0; lz < SIZE; lz++) {
			int kz = lz >> 2;
			float fz = (lz & 3) * 0.25f;
			long wz = baseZ + lz;
			for (int lx = 0; lx < SIZE; lx++) {
				int kx = lx >> 2;
				float fx = (lx & 3) * 0.25f;
				int base = kz * nyn + kx;
				boolean any = false;
				for (int gy = 0; gy < ny; gy++) {
					int i = base + gy * n;
					float a = g[i] + fx * (g[i + 1] - g[i]);
					float b = g[i + nyn] + fx * (g[i + nyn + 1] - g[i + nyn]);
					col[gy] = a + fz * (b - a);
					if (col[gy] > 0) any = true;
				}
				if (!any)
					continue;
				boolean biomeSet = false;
				byte top = GRASS, sub = DIRT;
				int run = 0; // solid voxels since the last air voxel above
				for (int ly = -8; ly < SIZE; ly++) {
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
						data = new byte[VOL];
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
						data = new byte[VOL];
					data[lx | (ly << SHIFT) | (lz << 2 * SHIFT)] = block;
				}
			}
		}
		return data;
	}

	// ---- 3D value noise (hash based: no table lookups, no cos(), works for any coordinate) ----

	private static double hash3(int x, int y, int z, int seed) {
		int h = x * 374761393 + y * 668265263 + z * 1274126177 + seed * 362437;
		h = (h ^ (h >>> 13)) * 1274126177;
		h ^= h >>> 16;
		return (h & 0xFFFFFF) * (1.0 / 0x1000000);
	}

	/** Smooth 3D value noise in [0, 1). */
	static double noise3(double x, double y, double z, int seed) {
		int xi = (int) Math.floor(x), yi = (int) Math.floor(y), zi = (int) Math.floor(z);
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
	private static final byte[] ORES        = { COAL_ORE, COPPER_ORE, IRON_ORE, GRAVEL,  COAL,  COPPER, IRON,    RUBY,  SAPPHIRE, AMETHYST, EMERALD };
	private static final byte[] ORE_HOST    = { STONE,    STONE,      STONE,    STONE,   SLATE, SLATE,  SLATE,   MAGMA, MAGMA,    MAGMA,    MOSS };
	private static final int[] ORE_PERCENT  = { 70,       45,         40,       25,      10,    6,      6,       2,     2,        2,        5 };     // chance per 16^3 cell
	private static final double[] ORE_R_MIN = { 1.5,      1.5,        1.5,      2.0,     1.0,   1.0,    1.0,     1.0,   1.0,      1.0,      1.0 };
	private static final double[] ORE_R_MAX = { 3.0,      2.5,        2.5,      2.5,     2.0,   1.8,    1.8,     1.6,   1.6,      1.6,      1.0 };  // keep <= 3 (see PAD)
	private static final double LAYER1 = 128, LAYER2 = 1024, LAYER_BLEND = 8;

	// Cave biomes (moss already existed; the other three are new)
	static final int CB_NONE = 0, CB_MOSS = 1, CB_SNOW = 2, CB_OBSIDIAN = 3, CB_CRYSTAL = 4;
	private static final int[] CB_ORDER = { CB_CRYSTAL, CB_OBSIDIAN, CB_SNOW, CB_MOSS }; // priority
	private static final byte[] CB_BLOCK = { AIR, MOSS, SNOW, OBSIDIAN, ASH };
	static final double BASIN_MAX_Y = 700, CRYSTAL_MAX_Y = 5000, OBSIDIAN_MAX_Y = 10000;

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
			if (band <= 0 || noise(wx / 512.0, wz / 512.0) <= 1.4) // only under snowy biomes
				return 0;
			return band * smoothstep(0.5, 0.7, noise3(wx / 160.0, cy / 90.0, wz / 160.0, 0x4E));
		}
		case CB_OBSIDIAN: return hardZone(wx, cy, wz, 0x4F, 80.0, 0.70, OBSIDIAN_MAX_Y);
		case CB_CRYSTAL:  return hardZone(wx, cy, wz, 0x50, 120.0, 0.64, CRYSTAL_MAX_Y);
		}
		return 0;
	}

	/** Same lookup for an arbitrary block position (snaps to the 4-block cell used by carveCaves). */
	private static double zoneAt(int biome, long x, long y, long z) {
		long s = CAVE_STEP;
		return zoneWeight(biome, Math.floorDiv(x, s) * s, Math.floorDiv(y, s) * s + s / 2.0, Math.floorDiv(z, s) * s);
	}

	private static boolean replaceable(int biome, byte cur) {
		if (biome >= CB_OBSIDIAN)
			return cur == MAGMA; // obsidian/crystal only ever replace magma
		return cur == STONE || cur == SLATE || cur == DIRT; // never the surface biome layer
	}

	/** Stone/slate boundary depth for this column. */
	private static double layer1(double wx, double wz) {
		return LAYER1 + (noise3(wx / 70.0, 0, wz / 70.0, 0x5A) - 0.5) * 96
				+ (noise3(wx / 20.0, 0, wz / 20.0, 0x5C) - 0.5) * 24;
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
		final int CELL = 16, PAD = 4; // PAD must exceed the largest blob radius
		long gx0 = Math.floorDiv(baseX - PAD, (long) CELL), gx1 = Math.floorDiv(baseX + SIZE - 1 + PAD, (long) CELL);
		long gy0 = Math.floorDiv(baseY - PAD, (long) CELL), gy1 = Math.floorDiv(baseY + SIZE - 1 + PAD, (long) CELL);
		long gz0 = Math.floorDiv(baseZ - PAD, (long) CELL), gz1 = Math.floorDiv(baseZ + SIZE - 1 + PAD, (long) CELL);

		for (int t = 0; t < ORES.length; t++) {
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

									if (ORE_HOST[t] != MOSS && isMossZone(x, y, z))
									    continue;

									data[idx] = ORES[t];
								}
					}
		}
	}

	/**
	 * "Spaghetti" caves: air wherever two independent 3D noise fields are both near zero. Carved per chunk inside
	 * generate() (thread-safe, seamless across borders, runs once per generated chunk), at every depth, and straight
	 * through the surface so entrances are visible. Trees/spires are planted afterwards and only on intact surface
	 * blocks with clear air above, so caves never cut through them.
	 */
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
	private static final byte[] ICE_MAT = { ICE }, CRYSTAL_MAT = { RUBY, SAPPHIRE, AMETHYST };
	private static final int ICICLE_ODDS = 4; // 1 in N cells attempts an icicle (lower = denser)

	private static void caveFeatures(long cx, long cy, long cz) {
		if (!caves)
			return;
		long baseX = cx * SIZE, baseY = cy * SIZE, baseZ = cz * SIZE;
		boolean snowY = baseY + SIZE > MOSS_Y0 && baseY < MOSS_Y3;
		boolean magmaY = baseY + SIZE > TBASE + LAYER2 - 300;
		byte[] d = world.chunk(cx, cy, cz);
		if ((!snowY && !magmaY) || d == null || d == World.UNLOADED)
			return;
		Random r = new Random(World.key(cx, cy, cz) ^ 0x1C1C1EL);
		for (int lx = 0; lx < SIZE; lx += 4)
			for (int ly = 0; ly < SIZE; ly += 4)
				for (int lz = 0; lz < SIZE; lz += 4) {
					if (r.nextInt(ICICLE_ODDS) != 0)
						continue;
					growIcicle(baseX + lx + r.nextInt(4), baseY + ly + r.nextInt(4), baseZ + lz + r.nextInt(4), r);
				}
	}

	private static void growIcicle(long wx, long wy, long wz, Random r) {
		icicle(wx, wy, wz, DIRS[r.nextInt(6)], r, true);
	}

	private static void icicle(long wx, long wy, long wz, int[] g, Random r, boolean needZone) {
		if (wy < 0 || getBlock(wx, wy, wz) != AIR)
			return;
		long sx = wx - g[0], sy = wy - g[1], sz = wz - g[2];
		byte base = getBlock(sx, sy, sz);
		int biome = base == SNOW ? CB_SNOW : base == ASH ? CB_CRYSTAL : CB_NONE;
		if (biome == CB_NONE || (needZone && zoneAt(biome, sx, sy, sz) <= 0))
			return;
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
			if (y < 0 || getBlock(x, y, z) != AIR)
				break;
			setBlock(x, y, z, block);
			if (i > 1 && i < 4) {
				arm(x, y, z, (ga + 1) % 3, 1, block);  arm(x, y, z, (ga + 1) % 3, -1, block);
				arm(x, y, z, (ga + 2) % 3, 1, block);  arm(x, y, z, (ga + 2) % 3, -1, block);
			}
		}
	}

	private static void arm(long x, long y, long z, int axis, int s, byte block) {
		long[] c = { x, y, z };
		c[axis] += s;
		if (getBlock(c[0], c[1], c[2]) == AIR)
			setBlock(c[0], c[1], c[2], block);
	}

	/** First y in [baseY, baseY+SIZE) holding `a` or `b` with air directly above, or -1. */
	private static long findSurface(long wx, long wz, long baseY, byte a, byte b) {
		for (long yy = baseY; yy < baseY + SIZE; yy++) {
			byte blk = getBlock(wx, yy, wz);
			if ((blk == a || blk == b) && getBlock(wx, yy - 1, wz) == AIR)
				return yy;
		}
		return -1;
	}

	// Cave basins: big open chambers inside the slate layer
	static final int BASIN_CELL = 160, BASIN_PAD = 64, BASIN_PERCENT = 22; // % of cells that hold a basin
	static final int BASIN_TRIES = 160, BASIN_TREE_TRIES = 14;
	private static final int[] DOWN = { 0, 1, 0 }, UP = { 0, -1, 0 }; // +y is down in this world

	/** {ox, oy, oz, rx, ry, rz, biome} for the basin owned by this 2D cell, or null. */
	private static double[] basinAt(long gx, long gz) {
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
			if (ty < 0 || Math.abs(ty - b[1]) > b[4] * 1.5)
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

	/**
	 * Spires and trees. Seeded per chunk column; each chunk plants only on surface blocks inside it. They are placed
	 * on the real, already-carved terrain: no tree on a cave mouth, and only where there is clear air for the trunk.
	 */
	private static void features(long cx, long cy, long cz) {
		long baseX = cx * SIZE, baseY = cy * SIZE, baseZ = cz * SIZE;
		long colKey = World.key(cx, 0, cz);
		for (int lx = 4; lx < SIZE - 4; lx += 8) {
			for (int lz = 4; lz < SIZE - 4; lz += 8) {
				long wx = baseX + lx, wz = baseZ + lz;
				long cell = colKey * 31 + lx * 7 + lz;

				Random r = new Random(cell ^ 0x51F1CEL);
				if (r.nextInt(20) == 0 && noise(wx / 512.0, wz / 512.0) >= 1.45) {
					int h = 6 + r.nextInt(6);
					long ty = findSurface(wx, wz, baseY, SNOW, ICE);
					if (ty >= 0) {
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

				r = new Random(cell ^ 0x7123L);
				if (r.nextInt(6) == 0) {
					long tx = wx + r.nextInt(32) - 16;
					long tz = wz + r.nextInt(32) - 16;
					int th = 4 + r.nextInt(2);
					double val = noise(tx / 512.0, tz / 512.0);
					if (val < 0.7 || val > 1.35)
						continue;
					long ty = findSurface(tx, tz, baseY, GRASS, GRASS);
					if (ty < 0)
						continue;
					boolean clear = true;
					for (long yy = ty - 1; yy >= ty - th - 2; yy--)
						if (getBlock(tx, yy, tz) != AIR) {
							clear = false;
							break;
						}
					if (clear)
						buildTree(tx, ty, tz, th, r);
				}
			}
		}
	}

	/** Trunk grows upward (decreasing y) from terrainY - 1. */
	private static void buildTree(long x, long terrainY, long z, int h, Random rand) {
		for (long yy = terrainY - 1; yy >= terrainY - h; yy--) {
			setBlock(x, yy, z, WOOD);
			if (getBlock(x, yy + 1, z) == GRASS)
				setBlock(x, yy + 1, z, DIRT);
		}
		fill(LEAVES, x - 2, terrainY - h + 1, z - 2, x + 3, terrainY - h + 3, z + 3, false);
		fill(LEAVES, x - 1, terrainY - h - 1, z - 1, x + 2, terrainY - h + 1, z + 2, false);
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
		byte[] c = world.chunk(x >> SHIFT, y >> SHIFT, z >> SHIFT);
		if (c == null || c == World.UNLOADED)
			return AIR;
		return c[(int) (x & MASK) | ((int) (y & MASK) << SHIFT) | ((int) (z & MASK) << 2 * SHIFT)];
	}

	static void setBlock(long x, long y, long z, byte block) {
		if (y < 0)
			return;
		long cx = x >> SHIFT, cy = y >> SHIFT, cz = z >> SHIFT;
		int s = world.slot(cx, cy, cz);
		if (world.keys[s] != World.key(cx, cy, cz))
			return;
		byte[] c = world.data[s];
		if (c == null) {
			if (block == AIR)
				return;
			c = world.data[s] = new byte[VOL];
		}
		int index = (int) (x & MASK) | ((int) (y & MASK) << SHIFT) | ((int) (z & MASK) << (2 * SHIFT));
		if (c[index] == block)
			return;
		c[index] = block;
		world.dirty[s] = true;
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

	private static void outline() {
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

	/** Iterative (the old recursive version could overflow the stack on big dynamite clusters). */
	private static void explode(long centerX, long centerY, long centerZ, int radius) {
		boom(centerX, centerY, centerZ);
		int r2 = radius * radius;
		Deque<long[]> stack = new ArrayDeque<>();
		stack.push(new long[] { centerX, centerY, centerZ });
		while (!stack.isEmpty()) {
			long[] c = stack.pop();
			for (long x = c[0] - radius; x <= c[0] + radius; x++)
				for (long y = c[1] - radius; y <= c[1] + radius; y++)
					for (long z = c[2] - radius; z <= c[2] + radius; z++) {
						long dx = x - c[0], dy = y - c[1], dz = z - c[2];
						if (dx * dx + dy * dy + dz * dz > r2)
							continue;
						byte block = getBlock(x, y, z);
						if (block == AIR)
							continue;
						setBlock(x, y, z, AIR);
						Particles.debris(x, y, z, block, c[0], c[1], c[2]);
						if (block == DYNAMITE)
							stack.push(new long[] { x, y, z });
					}
		}
	}

	/** Uses exactly the same 12 sample points as the collision code, so "overlaps" and "collides" always agree. */
	private static boolean intersectsPlayer(long bx, long by, long bz) {
		for (int c = 0; c < 12; c++) {
			long mx = (long) Math.floor(x + (c & 1) * 0.6 - 0.3);
			long my = (long) Math.floor(y + ((c >> 2) - 1) * 0.8 + 0.65);
			long mz = (long) Math.floor(z + (c >> 1 & 1) * 0.6 - 0.3);
			if (mx == bx && my == by && mz == bz)
				return true;
		}
		return false;
	}

	private static void click(int button) {
		long hx = hoveredX, hy = hoveredY, hz = hoveredZ;
		boolean has = hy != -1;
		if (fill) {
			if (has) {
				if (button == 1) {
					x0 = hx;
					y0 = hy;
					z0 = hz;
				} else if (button == 3) {
					x1 = hx;
					y1 = hy;
					z1 = hz;
				}
			}
		} else if (has) {
			if (button == 1) {
				block(getBlock(hx, hy, hz), 0, hx, hy, hz);
				Particles.burst(hx, hy, hz, getBlock(hx, hy, hz), 14, 0.04);
				setBlock(hx, hy, hz, AIR);
			}
			else if (button == 3) {
				long px = hx + dirX, py = hy + dirY, pz = hz + dirZ;
				if (hotbar[heldBlock] == AIR || !intersectsPlayer(px, py, pz)) {
					setBlock(px, py, pz, hotbar[heldBlock]);
					block(hotbar[heldBlock], 1, px, py, pz);
				}
			}
		}
		if (button == 3 && has && hotbar[heldBlock] == AIR) {
			byte b = getBlock(hx, hy, hz);
			if (b == DYNAMITE)
				explode(hx, hy, hz, power);
			else if (b == EMERALD)
				buildTree(hx, hy + 1, hz, 5, new Random());
		}
	}

	/** Middle click: switch to the hotbar page holding the looked-at block and select it. */
	private static void pick() {
		if (hoveredY == -1)
			return;
		byte id = getBlock(hoveredX, hoveredY, hoveredZ);
		if (id == AIR)
			return;
		if (xor) { // pages are locked in XOR mode: only blocks on that page can be picked
			for (int i = 0; i < XOR_PAGE.length; i++)
				if (XOR_PAGE[i] == id) {
					heldBlock = (byte) i;
					return;
				}
			return;
		}
		for (int p = 0; p < PAGES.length; p++)
			for (int i = 0; i < PAGES[p].length; i++)
				if (PAGES[p][i] == id) {
					page = p;
					heldBlock = (byte) i;
					return;
				}
	}

	// ------------------------------------------------------------------ textures

	private static void textures() {
		Random rand = new Random(7817105610522912629L);
		for (byte type = 1; type < BLOCK_COUNT; type++) {
			int gsd_tempA = 0;
			for (byte y = 0; y < texRes * 3; y++) {
				for (byte x = 0; x < texRes; x++) {
					int pattern, gsd_final, tint;
					if (xor) {
						if (type == GRASS || type == EMERALD) {
							pattern = (x ^ y) * 16 + 1;
							pattern = pattern << 8;
						} else if (type == DIRT || type == TOPAZ || type == SAND) {
							pattern = (x ^ y) * 16 + 1;
							pattern = pattern << 16 | pattern << 8;
						} else if (type == STONE) {
							pattern = (x ^ y) * 16 + 1;
						} else if (type == BRICKS || type == DYNAMITE) {
							pattern = (x ^ y) * 16 + 1;
							pattern = pattern << 16;
						} else if (type == WOOD || type == ICE) {
							pattern = (x ^ y) * 16 + 1;
							pattern |= pattern << 8;
						} else if (type == LEAVES) {
							pattern = (x ^ y) * 16 + 1;
							pattern |= pattern << 16;
						} else if (type == GLASS || type == SNOW) {
							pattern = (x ^ y) * 16 + 1;
							pattern |= pattern << 16 | pattern << 8;
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
						case GRASS:
							if (y < (((x * x * 3 + x * 81) / 2) % 4) + 18)
								tint = 0x7AFF40;
							else if (y < (((x * x * 3 + x * 81) / 2) % 4) + 19)
								gsd_tempA = gsd_tempA * 1 / 3;
							break;
						case WOOD:
							tint = 0x776644;
							byte wood = texRes / 2 - 1;
							int dx = x - wood;
							int dy = (y % texRes) - wood;
							if (dx < 0) dx = 1 - dx;
							if (dy < 0) dy = 1 - dy;
							if (dy > dx) dx = dy;
							double center = (Math.sqrt(dx * dx + dy * dy) * 0.25 + Math.max(dx, dy) * 0.75);
							if (y < 16 || y > 32) {
								if (center < texRes / 2) {
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
						default:
							if (type >= RUBY) {
								tint = extraTint(type, x, y);
								if (X_STYLE[type - RUBY] == 4)
									gsd_tempA = 0xFF;
							}
							break;
						}
						gsd_final = gsd_tempA;
						if (y >= texRes * 2)
							gsd_final /= 2;
						if (type == LEAVES) {
							tint = 0;
							double dx = Math.abs(x % 4 - 2) * 2;
							double dy = (y % 8) - 4;
							if (y / 8 % 2 == 1)
								dx = Math.abs((x + 2) % 4 - 2) * 2;
							dx += pNoise;
							double d = dx + Math.abs(dy);
							if (dy < 0)
								d = Math.sqrt(dx * dx + dy * dy);
							if (d < 3.5)
								tint = 0x00FF00;
							else if (d < 4)
								tint = 0x00CC00;
						}
						if (type == GLASS) {
							byte sizeX = texRes;
							byte sizeY = texRes;
							byte outline = 1;
							double localX = x % sizeX;
							double localY = y % sizeY;
							boolean border = localX < outline || localX > sizeX - (outline + 1) || localY < outline || localY > sizeY - (outline + 1);
							double[][] lines = {{sizeX / 3 - 2, 2 * sizeY / 3 - 2, sizeX / 3 + 2, 2 * sizeY / 3 + 2}, {2 * sizeX / 3 - 2, sizeY / 4 - 2, 2 * sizeX / 3 + 2, sizeY / 4 + 2}};
							boolean diagonal = false;
							for (double[] line : lines) {
								double startX = line[0], startY = line[1], endX = line[2], endY = line[3];
								if (localX >= Math.min(startX, endX) && localX <= Math.max(startX, endX) &&
										localY >= Math.min(startY, endY) && localY <= Math.max(startY, endY)) {
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
						atlas[x + y * texRes + type * (texRes * texRes) * 3] = col;
						continue;
					}
					int r = (pattern >> 16) & 0xFF;
					int g = (pattern >> 8) & 0xFF;
					int b = pattern & 0xFF;
					int color = (0xFF << 24) | (r << 16) | (g << 8) | b;
					atlas[x + y * texRes + type * (texRes * texRes) * 3] = color;
				}
			}
		}
	}

	private static int extraTint(int type, int x, int y) {
		int i = type - RUBY, base = X_BASE[i], acc = X_ACCENT[i];
		int lx = x & 15, ly = y & 15;
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

	private void gui(Graphics2D g2d) {
		byte[] hb = hotbar;
		int sc = scale;
		if (guiFont == null || guiFontScale != sc) {
			guiFont = new Font("Palatino Linotype", 1, 16 * sc);
			guiFontScale = sc;
		}
		lineH = 18 * sc;
		gy = 16 * sc;

		double usedMem = (Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory()) / 1048576.0;
		int slot = 40 * sc;
		int padding = 2 * sc;
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
					0, texRes * (hb[i] * 3 + 1), texRes, texRes * (hb[i] * 3 + 2), null);
		}
		g2d.setColor(Color.white);
		g2d.setStroke(new BasicStroke(3 * sc));
		g2d.drawRect(hotbarX + heldBlock * slot, hotbarY, slot, slot);
		g2d.setFont(guiFont);

		if (option == 0) {
			if (showFPS) {
				g2d.setColor(Color.red);
				if (vSync) {
					ln(g2d, fps + " FPS (VSync)");
				} else {
					ln(g2d, fps + " FPS");
				}
			}
			if (showXYZ) {
				g2d.setColor(Color.yellow);
				ln(g2d, "X: " + format(x, FMT3));
				ln(g2d, "Y: " + format(y, FMT3));
				ln(g2d, "Z: " + format(z, FMT3));
			}
			if (showRot) {
				long fx = (long) Math.floor(x), fy = (long) Math.floor(y), fz = (long) Math.floor(z);
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
				ln(g2d, "Zoom: " + (short) zoom + " (Switch: " + zoomSwitch + ")");
				ln(g2d, "Render Distance: " + dist + " (" + radius + ")");
			}
			if (showMagenta) {
				g2d.setColor(Color.magenta);
				ln(g2d, "Window Size: " + width + "x" + height + " (" + resX + "x" + resY + ", " + detail + ")");
				String mode = classic && xor ? "Retro" : xor ? "Bitwise" : classic ? "Classic" : "Complex";
				ln(g2d, "Render Mode: " + mode);
			}
			if (showExtra) {
				g2d.setColor(Color.white);
				ln(g2d, String.format("RAM Used: %.1fMB", usedMem));
				ln(g2d, "Hotbar Page: " + (page + 1) + "/" + PAGES.length + " (particles: " + (particlesOn ? String.valueOf(Particles.count) : "off") + ")");
				if (fly)
					ln(g2d, "Flight enabled!");
				if (hoveredY != -1)
					ln(g2d, "Looking at (" + hoveredX + ", " + hoveredY + ", " + hoveredZ + ") : " + hoveredType);
				if (fill) {
					ln(g2d, "Fill mode active!");
					ln(g2d, "Block A: (" + x0 + ", " + y0 + ", " + z0 + ")");
					ln(g2d, "Block B: (" + x1 + ", " + y1 + ", " + z1 + ")");
				}
				if (System.currentTimeMillis() - locMsgTime < 5000) {
					g2d.setColor(new Color(255, 127, 0));
					ln(g2d, locMsg);
				}
			}
		} else if (option == 2) {
			g2d.setColor(Color.white);
			ln(g2d, VERSION + ", made on October 10, 2026");
			g2d.setColor(Color.red);
			ln(g2d, "Interface controls: F1 for main, F2 to hide text, F4 to hide all");
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
			ln(g2d, "Change Block Type: [1-" + hb.length + "] or Scroll Wheel (disabled if zoom scroll is active)");
			ln(g2d, "Change Pixel Scale: P+ / M-");
			ln(g2d, "Toggle Display Debug: F5+[1-6] - U to reset");
			ln(g2d, "Toggle VSync: F6");
			ln(g2d, "Toggle Sounds: K");
			g2d.setColor(Color.magenta);
			ln(g2d, "Toggle Classic Mode: C");
			ln(g2d, "Toggle Bitwise Mode: X");
			ln(g2d, "Toggle Zoom Scroll: Z + Scroll Wheel");
			ln(g2d, "Switch Hotbar: Q/E");
			ln(g2d, "Reset Rotation: T");
			ln(g2d, "Change Lighting: L");
			g2d.setColor(Color.white);
			ln(g2d, "Fill Mode: F7; Left/Right Click to set Block A/B; F8 to execute, places held block");
			ln(g2d, "Spawn Chunk Outline: G");
			ln(g2d, "Toggle Particles: V");
			ln(g2d, "Open Dialog (Modify Data): F10");
			ln(g2d, "Save/Load World: F9 / F12");
			ln(g2d, "Toggle Fullscreen: F11");
			ln(g2d, "Locate Feature: N to cycle target, B to teleport");
		}
	}

	@Override
	public void paint(Graphics g) {
		Graphics2D g2d = (Graphics2D) g;
		BufferedImage img = screen;
		g2d.drawImage(img, 0, 0, width, height, null);
		if (display) {
			g2d.drawImage(crosshair, width / 2 - CROSS / 2, height / 2 - CROSS / 2, null);
			gui(g2d);
		}
	}

	/** Main thread only. */
	private static void update() {
		int wd = width;
		if (wd != zoomWidth) {
			zoomWidth = wd;
			scale = (byte) autoGuiScale(wd);
			zoom = autoZoom(wd);
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

	private void save() {
	    JFileChooser fc = new JFileChooser();
	    fc.setDialogTitle("Save");
	    chooser(fc);

	    if (fc.showSaveDialog(frame) != 0)
	        return;

	    File file = fc.getSelectedFile();

	    if (file.exists()) {
	        int result = JOptionPane.showConfirmDialog(
	            frame,
	            "A file with this name already exists.\nDo you want to overwrite it?",
	            "Confirm Overwrite",
	            0, 2
	        );
	        if (result != 0) return;
	    }

	    tasks.add(() -> doSave(file));
	}

	private void load() {
	    JFileChooser fc = new JFileChooser();
	    fc.setDialogTitle("Load");
	    chooser(fc);

	    if (fc.showOpenDialog(frame) != 0)
	        return;

	    File file = fc.getSelectedFile();
	    tasks.add(() -> doLoad(file));
	}

	private static void doSave(File file) {
		flushDirty();
		Path target = file.toPath();
		Path tmp = target.resolveSibling(target.getFileName() + ".tmp");
		try {
			try (DataOutputStream out = new DataOutputStream(new BufferedOutputStream(Files.newOutputStream(tmp), 1 << 16))) {
				out.writeInt(MAGIC);
				out.writeDouble(x);
				out.writeDouble(y);
				out.writeDouble(z);
				out.writeDouble(yaw);
				out.writeDouble(pitch);
				out.writeShort(dist);
				out.writeLong(time);
				out.writeBoolean(caves);
				out.writeBoolean(terrain3D);
				out.writeDouble(amp);
				out.writeDouble(red);
				out.writeDouble(green);
				out.writeDouble(blue);
				out.writeBoolean(classic);
				out.writeBoolean(xor);

				Map<Long, byte[]> sorted = new TreeMap<>(savedChunks);
				out.writeInt(sorted.size());

				// finish() instead of close(), because closing would also close `out`.
				Deflater def = new Deflater(Deflater.BEST_COMPRESSION);
				try {
					DeflaterOutputStream z = new DeflaterOutputStream(out, def, 1 << 16);
					DataOutputStream cd = new DataOutputStream(z);
					for (Map.Entry<Long, byte[]> e : sorted.entrySet()) {
						byte[] blob = e.getValue();
						cd.writeLong(e.getKey());
						cd.writeInt(blob.length);
						cd.write(blob);
					}
					cd.flush();
					z.finish();
				} finally {
					def.end();
				}
			}
			try {
				Files.move(tmp, target, StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE);
			} catch (AtomicMoveNotSupportedException ex) {
				Files.move(tmp, target, StandardCopyOption.REPLACE_EXISTING);
			}
		} catch (Exception e) {
			e.printStackTrace();
			try { Files.deleteIfExists(tmp); } catch (IOException ignored) {}
			JOptionPane.showMessageDialog(frame, "Failed to save world:\n" + e.getMessage());
		}
	}

	private static void doLoad(File file) {
		final int MAX_BLOB = 2 * VOL + 16; // worst case: alternating blocks, 2 bytes each
		try (DataInputStream in = new DataInputStream(new BufferedInputStream(Files.newInputStream(file.toPath()), 1 << 16))) {
			if (in.readInt() != MAGIC) {
				JOptionPane.showMessageDialog(frame, "Unsupported save file (not a Bitwise Nexus save)");
				return;
			}

			// Parse everything into locals first; only touch the game state once the whole file is valid.
			double nx = in.readDouble(), ny = in.readDouble(), nz = in.readDouble();
			double nYaw = in.readDouble(), nPitch = in.readDouble();
			short nDist = in.readShort();
			long nTime = in.readLong();
			boolean nCaves = in.readBoolean(), nT3 = in.readBoolean();
			double nAmp = in.readDouble(), nRed = in.readDouble(), nGreen = in.readDouble(), nBlue = in.readDouble();
			boolean nClassic = in.readBoolean(), nXor = in.readBoolean();

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
			}

			x = nx;
			y = ny;
			z = nz;
			yaw = nYaw;
			pitch = nPitch;
			time = nTime;
			caves = nCaves;
			terrain3D = nT3;
			amp = nAmp;
			red = nRed;
			green = nGreen;
			blue = nBlue;
			classic = nClassic;
			xor = nXor;
			textures();
			velX = velY = velZ = 0;

			setDist(nDist);
			world.clear();
			savedChunks.clear();
			savedChunks.putAll(loaded);
			chunkLastSeen.clear();
			Particles.clear();

			lcx = Long.MIN_VALUE;
			lcy = 0;
			lcz = 0;
			chunkDirty = true;
			needGround = false;
		} catch (Exception e) {
			e.printStackTrace();
			JOptionPane.showMessageDialog(frame, "Failed to load world:\n" + e.getMessage());
		}
	}

	/** Runs of (value byte, varint run length). A uniform chunk is ~4 bytes instead of ~2 KB. */
	private static byte[] encode(byte[] data) {
		byte[] out = new byte[1024];
		int n = 0, i = 0;
		final int len = data.length;
		while (i < len) {
			byte v = data[i];
			int j = i + 1;
			while (j < len && data[j] == v)
				j++;
			int run = j - i;
			if (n + 6 > out.length)
				out = Arrays.copyOf(out, out.length * 2);
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

	private static byte[] decode(byte[] data) {
		byte[] out = new byte[VOL];
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

	private static JTextField row(JPanel p, String label, Object value, Color c, Font lf, Font tf) {
		JLabel l = new JLabel(label);
		l.setFont(lf);
		l.setForeground(c);
		JTextField t = new JTextField(String.valueOf(value));
		t.setFont(tf);
		p.add(l);
		p.add(t);
		return t;
	}

	private static void dialog() {
		JPanel panel = new JPanel(new GridLayout(0, 2, 0, scale));
		Font lf = new Font("Arial", 1, 12 * scale);
		Font tf = new Font("Dialog", 0, 12 * scale);
		JTextField xF = row(panel, "X Coordinate:", x, Color.red, lf, tf);
		JTextField yF = row(panel, "Y Coordinate:", y, Color.red, lf, tf);
		JTextField zF = row(panel, "Z Coordinate:", z, Color.red, lf, tf);
		JTextField tF = row(panel, "Time:", time, Color.blue, lf, tf);
		JTextField aF = row(panel, "Amplitude:", amp, Color.blue, lf, tf);
		JTextField fF = row(panel, "Flight Speed:", flight, Color.magenta, lf, tf);
		JTextField rF = row(panel, "Render Distance:", dist, Color.magenta, lf, tf);
		JTextField redF = row(panel, "Fog Red:", red, Color.red, lf, tf);
		JTextField greenF = row(panel, "Fog Green:", green, Color.green, lf, tf);
		JTextField blueF = row(panel, "Fog Blue:", blue, Color.blue, lf, tf);
		JTextField eF = row(panel, "Explosion Power:", power, Color.black, lf, tf);
		JTextField gF = row(panel, "GUI Scale:", scale, Color.black, lf, tf);
		JTextField sF = row(panel, "Mouse Sensitivity:", sensitivity, Color.black, lf, tf);
		JCheckBox dBox = new JCheckBox("Use Degrees for Rotation", degrees);
		JCheckBox cBox = new JCheckBox("Enable Cave Generation", caves);
		JCheckBox tBox = new JCheckBox("3D Terrain", terrain3D);
		for (JCheckBox b : new JCheckBox[] { dBox, cBox, tBox }) {
			b.setFont(lf);
			b.setForeground(Color.black);
			panel.add(b);
		}
		if (JOptionPane.showConfirmDialog(frame, panel, "Modify Data", 2) == 0) {
			try {
				final double nx = Double.parseDouble(xF.getText()), ny = Double.parseDouble(yF.getText()), nz = Double.parseDouble(zF.getText());
				final long nt = Long.parseLong(tF.getText());
				final double na = Double.parseDouble(aF.getText()), nf = Double.parseDouble(fF.getText()), ns = Double.parseDouble(sF.getText());
				final double nRed = Double.parseDouble(redF.getText()), nGreen = Double.parseDouble(greenF.getText()), nBlue = Double.parseDouble(blueF.getText());
				final int nd = Integer.parseInt(rF.getText());
				final byte np = Byte.parseByte(eF.getText());
				final byte nsc = (byte) Math.max(1, Math.min(3, Integer.parseInt(gF.getText())));
				final boolean nDeg = dBox.isSelected(), nCaves = cBox.isSelected(), nT3 = tBox.isSelected();
				tasks.add(() -> {
					boolean terrain = nCaves != caves || nT3 != terrain3D || na != amp;
					boolean moved = nx != x || nz != z;
					x = nx;
					y = ny;
					z = nz;
					time = nt;
					amp = na;
					flight = nf;
					sensitivity = ns;
					red = nRed;
					green = nGreen;
					blue = nBlue;
					power = np;
					scale = nsc;
					degrees = nDeg;
					caves = nCaves;
					terrain3D = nT3;
					setDist(nd);
					if (terrain) {
						flushDirty();
						world.clear();
						chunkLastSeen.clear();
					}
					if (terrain || moved) {
						y = groundY(x, z);
						needGround = true;
						Particles.clear();
					}
					chunkDirty = true;
				});
			} catch (NumberFormatException ex) {
				JOptionPane.showMessageDialog(frame, "Invalid number: " + ex.getMessage());
			}
		}
		synchronized (input) {
			input.clear();
		}
	}

	// ------------------------------------------------------------------ feature locator (N = cycle target, B = teleport)
	static final String[] LOC_NAMES = { "Moss Basin", "Snow Basin", "Moss Cave", "Snow Cave", "Obsidian Cave", "Crystal Cave", "Snowy Biome", "Icy Biome", "Desert Biome", "Plains Biome" };
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
		boolean ok = t == 6 ? n > 1.4 && n < 1.85 : t == 7 ? n > 1.85 : t == 8 ? n < 0.65 : n > 0.8 && n < 1.3;
		return ok ? new double[] { wx + 0.5, 0, wz + 0.5 } : null;
	}

	/** One grid cell (gx, gz) for the given target; returns a world {x, y, z} or null. */
	private static double[] probe(int t, long gx, long gz, int cell) {
		if (t < 2) {
			double[] b = basinAt(gx, gz);
			int want = t == 0 ? CB_MOSS : CB_SNOW;
			return b != null && (int) b[6] == want ? new double[] { b[0], b[1], b[2] } : null;
		}
		long wx = gx * cell + cell / 2, wz = gz * cell + cell / 2;
		return t < 6 ? caveProbe(t - 1, wx, wz) : surfaceProbe(t, wx, wz);
	}

	/** Square rings of grid cells around (cx, cz), nearest rings first. */
	private static double[] search(int t, long px, long pz) {
		int cell = t < 2 ? BASIN_CELL : t < 6 ? 32 : 64;
		int rings = t < 2 ? 40 : t < 6 ? 150 : 120;
		long cx = Math.floorDiv(px, (long) cell), cz = Math.floorDiv(pz, (long) cell);
		for (int r = 0; r <= rings; r++)
			for (long dx = -r; dx <= r; dx++)
				for (long dz = -r; dz <= r; dz += (Math.abs(dx) == r || r == 0) ? 1 : 2 * r) {
					double[] hit = probe(t, cx + dx, cz + dz, cell);
					if (hit != null)
						return hit;
				}
		return null;
	}

	private static void teleport(double[] p, boolean ground) {
		tasks.add(() -> {
			x = p[0];
			y = p[1];
			z = p[2];
			prevX = x; prevY = y; prevZ = z;
			velX = velY = velZ = 0;
			Particles.clear();
			chunkDirty = true;
			needGround = ground; // surface targets: snap to the real ground once chunks exist
		});
	}

	private static void locate(int t) {
		if (t < 6 && !caves) {
			say("Enable caves first (F10)");
			return;
		}
		if (!locBusy.compareAndSet(false, true))
			return;
		final long px = (long) Math.floor(x), pz = (long) Math.floor(z);
		say("Searching for " + LOC_NAMES[t] + "...");
		Thread th = new Thread(() -> {
			try {
				double[] hit = search(t, px, pz);
				if (hit == null) {
					say(LOC_NAMES[t] + ": none found nearby");
				} else {
					say(String.format("%s at (%.0f, %.0f, %.0f)", LOC_NAMES[t], hit[0], hit[1], hit[2]));
					teleport(hit, t >= 6);
				}
			} finally {
				locBusy.set(false);
			}
		}, "nexus-locate");
		th.setDaemon(true);
		th.start();
	}

	@Override
	public void keyPressed(KeyEvent e) {
		activity = System.currentTimeMillis();
		int code = e.getKeyCode();
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
		case KeyEvent.VK_F10:
			dialog();
			break;
		case KeyEvent.VK_F9:
			save();
			break;
		case KeyEvent.VK_F11:
			toggleFullscreenRequested = true;
			break;
		case KeyEvent.VK_F12:
			load();
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
	    if (toggleFullscreenRequested)
	        return;

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
		final int b = e.getButton();
		if (b == 1 || b == 3)
			tasks.add(() -> click(b));
		else if (b == 2)
			tasks.add(Nexus::pick);
	}

	@Override
	public void mouseReleased(MouseEvent e) {}

	@Override
	public void mouseEntered(MouseEvent e) {
		center();
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
	}

	@Override
	public void focusLost(FocusEvent e) {
		lock = true;
		focus = false;
		synchronized (input) {
			input.clear(); // avoid stuck keys after alt-tab
		}
	}

	@Override
	public void mouseWheelMoved(MouseWheelEvent e) {
		if (zoomSwitch) {
			if (e.getUnitsToScroll() < 0) {
				zoom *= 1.1;
				if (zoom > 5000) zoom = 5000;
			} else {
				zoom /= 1.1;
				if (zoom < 10) zoom = 10;
			}
		} else {
			int len = hotbar.length;
			int h = heldBlock + (e.getUnitsToScroll() < 0 ? -1 : 1);
			if (h < 0) h = len - 1;
			if (h >= len) h = 0;
			heldBlock = (byte) h;
		}
	}

	public void keyTyped(KeyEvent e) {}
}

final class World {
	static final byte[] UNLOADED = new byte[0];
	static final long NONE = Long.MIN_VALUE;
	int w;
	long[] keys;
	byte[][] data;
	boolean[] dirty;

	World(int radius) {
		resize(radius);
	}

	void resize(int radius) {
		w = 2 * radius + 1;
		int n = w * w * w;
		keys = new long[n];
		data = new byte[n][];
		dirty = new boolean[n];
		clear();
	}

	void clear() {
		Arrays.fill(keys, NONE);
		Arrays.fill(data, null);
		Arrays.fill(dirty, false);
	}

	/** 21 bits per axis, packed - unique (the old 31-multiplier hash collided). */
	static long key(long cx, long cy, long cz) {
		return (cx & 0x1FFFFF) << 42 | (cy & 0x1FFFFF) << 21 | (cz & 0x1FFFFF);
	}

	static long[] decodeKey(long key) {
	    long cx = (key >>> 42) & 0x1FFFFF;
	    long cy = (key >>> 21) & 0x1FFFFF;
	    long cz = key & 0x1FFFFF;

	    if ((cx & 0x100000) != 0)
	        cx |= ~0x1FFFFFL;

	    if ((cy & 0x100000) != 0)
	        cy |= ~0x1FFFFFL;

	    if ((cz & 0x100000) != 0)
	        cz |= ~0x1FFFFFL;

	    return new long[] { cx, cy, cz };
	}

	static long unpackX(long k) { return (k << 1) >> 43; }
	static long unpackY(long k) { return (k << 22) >> 43; }
	static long unpackZ(long k) { return (k << 43) >> 43; }

	int slot(long cx, long cy, long cz) {
		int ix = (int) (cx % w), iy = (int) (cy % w), iz = (int) (cz % w);
		if (ix < 0) ix += w;
		if (iy < 0) iy += w;
		if (iz < 0) iz += w;
		return (ix * w + iy) * w + iz;
	}

	boolean has(long cx, long cy, long cz) {
		return keys[slot(cx, cy, cz)] == key(cx, cy, cz);
	}

	byte[] chunk(long cx, long cy, long cz) {
		int s = slot(cx, cy, cz);
		return keys[s] == key(cx, cy, cz) ? data[s] : UNLOADED;
	}

	void put(long cx, long cy, long cz, byte[] d) {
		int s = slot(cx, cy, cz);
		data[s] = d;
		dirty[s] = false;
		keys[s] = key(cx, cy, cz);
	}

	void remove(long cx, long cy, long cz) {
		int s = slot(cx, cy, cz);
		if (keys[s] == key(cx, cy, cz)) {
			keys[s] = NONE;
			data[s] = null;
			dirty[s] = false;
		}
	}
}

final class Render implements Callable<Void> {
	static int[] out;
	static int w, h;
	static double[] colX = new double[0], rowY = new double[0];
	static float[] invLen = new float[0];
	static double maxDist, px, py, pz, lx, ly, lz;
	static long pbx, pby, pbz;
	static double cachedZoom = Double.NaN;
	static int cachedW, cachedH;
	static double sunR, sunG, sunB, ambR, ambG, ambB, skyR, skyG, skyB;
	static boolean cls, hl;
	static long hvX, hvY, hvZ;
	static final AtomicInteger next = new AtomicInteger();
	static final double INF = Double.POSITIVE_INFINITY, EPS = 1e-4;
	static float[] depth = new float[0];
	static double xScale, yScale, shadowDist;
	static int cachedWinW, cachedWinH;
	static final double SHADOW_RANGE = 128;

	static void prepare() {
		out = buffer;
		w = resX;
		h = resY;
		final int ww = width, wh = height;
		if (colX.length != w) colX = new double[w];
		if (rowY.length != h) rowY = new double[h];
		if (invLen.length != w * h) invLen = new float[w * h];
		if (depth.length != w * h) depth = new float[w * h];
		double invZoom = 1.0 / zoom;
		xScale = invZoom * ww / (4.0 * w);
		yScale = invZoom * wh / (4.0 * h);
		if (cachedW != w || cachedH != h || cachedZoom != zoom || cachedWinW != ww || cachedWinH != wh) {
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
			cachedZoom = zoom;
			cachedWinW = ww;
			cachedWinH = wh;
		}
		shadowDist = Math.min(dist, SHADOW_RANGE);
		maxDist = dist;
		cls = classic;
		hl = display;
		hvX = hoveredX;
		hvY = hoveredY;
		hvZ = hoveredZ;
		px = Nexus.viewX;
		py = Nexus.viewY;
		pz = Nexus.viewZ;
		pbx = (long) Math.floor(px);
		pby = (long) Math.floor(py);
		pbz = (long) Math.floor(pz);
		lx = light.x;
		ly = light.y;
		lz = light.z;
		sunR = sunColor.x; sunG = sunColor.y; sunB = sunColor.z;
		ambR = ambColor.x; ambG = ambColor.y; ambB = ambColor.z;
		skyR = skyColor.x; skyG = skyColor.y; skyB = skyColor.z;
		prepareFog();
		next.set(0);
	}

	private long ccx, ccy, ccz;
	private byte[] cchunk;
	// last hit
	private double hT, hHx, hHy, hHz, hR, hG, hB;
	private int hAxis, hSign;
	static double cave, fLR = 1, fLG = 1, fLB = 1, fogCamR, fogCamG, fogCamB;
	static final Fog camFog = new Fog();
	private final Fog fog = new Fog();
	private long hBx, hBy, hBz;
	private int hId;
	// Secondary-ray memoization: adjacent screen pixels commonly hit the same voxel face.
	private static final int LIGHT_CACHE_SIZE = 512;
	private final long[] skyX = new long[LIGHT_CACHE_SIZE], skyY = new long[LIGHT_CACHE_SIZE], skyZ = new long[LIGHT_CACHE_SIZE];
	private final double[] skyValue = new double[LIGHT_CACHE_SIZE];
	private final boolean[] skyUsed = new boolean[LIGHT_CACHE_SIZE];

	@Override
	public Void call() {
		Arrays.fill(skyUsed, false);
		ccx = ccy = ccz = Long.MIN_VALUE;
		cchunk = null;
		int row;
		while ((row = next.getAndIncrement()) < h)
			renderRow(row);
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

	private void renderRow(int row) {
		int base = row * w;
		double fy = rowY[row];
		double sp = sinPitch, cp = cosPitch, sy = sinYaw, cy = cosYaw;
		double temp = cp + fy * sp;
		double dyBase = fy * cp - sp;
		for (int col = 0; col < w; col++) {
			double fx = colX[col];
			double inv = invLen[base + col];
			double dx = (fx * cy + temp * sy) * inv;
			double dy = dyBase * inv;
			double dz = (temp * cy - fx * sy) * inv;
			boolean center = col == w / 2 && row == h / 2;
			double r, g, b;
			depth[base + col] = Float.MAX_VALUE;
			if (march(px, py, pz, dx, dy, dz, maxDist, true, center)) {
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
			int ri = Math.min(255, Math.max(0, (int) (r * 255)));
			int gi = Math.min(255, Math.max(0, (int) (g * 255)));
			int bi = Math.min(255, Math.max(0, (int) (b * 255)));
			out[base + col] = ri << 16 | gi << 8 | bi;
		}
	}

	/**
	 * Amanatides-Woo voxel traversal. Returns true on the first opaque texel; results go in the h* fields.
	 * Rays leaving the world (above y=0, or out of the loaded chunk window) terminate immediately.
	 */
	private boolean march(double ox, double oy, double oz, double dx, double dy, double dz, double maxT, boolean primary, boolean center) {
		long bx, by, bz;
		if (primary) {
			bx = pbx; by = pby; bz = pbz;
		} else {
			bx = (long) Math.floor(ox);
			by = (long) Math.floor(oy);
			bz = (long) Math.floor(oz);
		}
		int sx = dx > 0 ? 1 : dx < 0 ? -1 : 0;
		int sy = dy > 0 ? 1 : dy < 0 ? -1 : 0;
		int sz = dz > 0 ? 1 : dz < 0 ? -1 : 0;
		double tdx = sx == 0 ? INF : 1.0 / Math.abs(dx);
		double tdy = sy == 0 ? INF : 1.0 / Math.abs(dy);
		double tdz = sz == 0 ? INF : 1.0 / Math.abs(dz);
		double tmx = sx == 0 ? INF : (sx > 0 ? (double) bx + 1 - ox : ox - bx) * tdx;
		double tmy = sy == 0 ? INF : (sy > 0 ? (double) by + 1 - oy : oy - by) * tdy;
		double tmz = sz == 0 ? INF : (sz > 0 ? (double) bz + 1 - oz : oz - bz) * tdz;
		boolean hoverPending = primary && center;

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
			if (by < 0) {
				if (sy <= 0)
					return false; // heading into the sky forever
				continue;
			}
			long cx = bx >> SHIFT, cy = by >> SHIFT, cz = bz >> SHIFT;
			if (cx != ccx || cy != ccy || cz != ccz) {
				ccx = cx;
				ccy = cy;
				ccz = cz;
				cchunk = world.chunk(cx, cy, cz);
			}
			byte[] chunk = cchunk;
			if (chunk == World.UNLOADED)
				return false;
			int id = chunk == null ? 0 : chunk[(int) (bx & MASK) | ((int) (by & MASK) << SHIFT) | ((int) (bz & MASK) << 2 * SHIFT)];
			if (id == AIR)
				continue;

			// Glass is a single continuous volume: do not draw faces between
			// adjacent glass voxels, including across chunk boundaries.
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
				texX = (int) tex16(hx * texRes);
				texY = (int) tex16(hz * texRes);
				if (dy < 0.0)
					texY += texRes * 2;
			} else {
				texX = (int) tex16((hx + hz) * texRes);
				texY = (int) tex16(hy * texRes) + texRes;
			}
			int step = axis == 0 ? sx : axis == 1 ? sy : sz;

			if (hoverPending) {
				hoverPending = false;
				if (t < reach) {
					newHoverX = bx;
					newHoverY = by;
					newHoverZ = bz;
					hoveredType = getType((byte) id);
					newDirX = axis == 0 ? -step : 0;
					newDirY = axis == 1 ? -step : 0;
					newDirZ = axis == 2 ? -step : 0;
				}
			}

			int c;
			if (primary && hl && bx == hvX && by == hvY && bz == hvZ && (texX == 0 || texY % texRes == 0 || texX == texRes - 1 || texY % texRes == texRes - 1))
				c = 0xFFFFFF;
			else
				c = atlas[texX + texY * texRes + id * TEX_STRIDE];
			if ((c & 0xFFFFFF) == 0)
				continue; // transparent texel

			hT = t;
			hBx = bx;
			hBy = by;
			hBz = bz;
			hId = id;
			hAxis = axis;
			hSign = -step;
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

	/** Per-frame fog setup: time-of-day tint for fog colours and the camera's own fog colour. */
	static void prepareFog() {
		cave = Nexus.caveMix;
		if (cls) {
			fLR = fLG = fLB = 1;
		} else {
			double lv = 0.12 + 0.88 * Nexus.daylight();
			double m = Math.max(1e-3, Math.max(skyR, Math.max(skyG, skyB)));
			fLR = lv * (0.65 + 0.35 * skyR / m);
			fLG = lv * (0.65 + 0.35 * skyG / m);
			fLB = lv * (0.65 + 0.35 * skyB / m);
		}
		camFog.at(px, py, pz);
		fogCamR = camFog.r; fogCamG = camFog.g; fogCamB = camFog.b;
	}

	/** Classic: flat face shading + biome fog blend. */
	private void shadeClassic() {
		fog.at(hHx, hHy, hHz);
		double ft = Math.min(1, hT * fog.dens / maxDist);
		double s = (0xFF - (hAxis + 2) % 3 * 50) / 255.0 * (1 - ft);
		hR = hR * s + fog.r * ft;
		hG = hG * s + fog.g * ft;
		hB = hB * s + fog.b * ft;
	}

	private boolean solid(long x, long y, long z) {
		if (y < 0)
			return false;
		long cx = x >> SHIFT, cy = y >> SHIFT, cz = z >> SHIFT;
		if (cx != ccx || cy != ccy || cz != ccz) {
			ccx = cx; ccy = cy; ccz = cz;
			cchunk = world.chunk(cx, cy, cz);
		}
		byte[] c = cchunk;
		if (c == null || c == World.UNLOADED)
			return false;
		return c[(int) (x & MASK) | ((int) (y & MASK) << SHIFT) | ((int) (z & MASK) << 2 * SHIFT)] != AIR;
	}

	private int occ(long x, long y, long z, int axis, int i, int j) {
		boolean s;
		switch (axis) {
		case 0: s = solid(x, y + i, z + j); break;
		case 1: s = solid(x + i, y, z + j); break;
		default: s = solid(x + i, y + j, z);
		}
		return s ? 1 : 0;
	}

	private static int vertexAO(int s1, int s2, int c) {
		return s1 == 1 && s2 == 1 ? 0 : 3 - (s1 + s2 + c);
	}

	/** Per-vertex voxel ambient occlusion, bilinearly interpolated over the face. 0 = dark, 1 = open. */
	private double aoAt(long x, long y, long z, int a, double fu, double fv) {
		int um = occ(x, y, z, a, -1, 0), up = occ(x, y, z, a, 1, 0);
		int vm = occ(x, y, z, a, 0, -1), vp = occ(x, y, z, a, 0, 1);
		double a00 = vertexAO(um, vm, occ(x, y, z, a, -1, -1)), a10 = vertexAO(up, vm, occ(x, y, z, a, 1, -1));
		double a01 = vertexAO(um, vp, occ(x, y, z, a, -1, 1)),  a11 = vertexAO(up, vp, occ(x, y, z, a, 1, 1));
		double lo = a00 + (a10 - a00) * fu, hi = a01 + (a11 - a01) * fu;
		return (lo + (hi - lo) * fv) / 3.0;
	}

	/** Sky exposure cached per voxel; many neighbouring pixels hit the same block. */
	private static final double[][] SKY_OFFSETS = {{0,0},{0.72,0},{-0.72,0},{0,0.72},{0,-0.72}};

	private double skyLight(long fx, long fy, long fz) {
		long hash = fx * 0x9E3779B97F4A7C15L ^ Long.rotateLeft(fy * 0xC2B2AE3D27D4EB4FL, 17) ^ Long.rotateLeft(fz, 37);
		int i = (int) (hash ^ (hash >>> 32)) & (LIGHT_CACHE_SIZE - 1);
		if (skyUsed[i] && skyX[i] == fx && skyY[i] == fy && skyZ[i] == fz)
			return skyValue[i];
		// Average a small bundle of vertical rays. A lone block directly overhead
		// should only affect one sample, not create a conspicuous dark spot in daylight.
		double total = 0;
		for (double[] o : SKY_OFFSETS) {
			double ox = fx + 0.5 + o[0], oz = fz + 0.5 + o[1];
			boolean blocked = march(ox, fy + 0.5, oz, 0, -1, 0, 64, false, false);
			total += blocked ? Math.min(1, hT / 24.0) * 0.5 : 1.0;
		}
		double value = total / SKY_OFFSETS.length;
		skyUsed[i] = true; skyX[i] = fx; skyY[i] = fy; skyZ[i] = fz; skyValue[i] = value;
		return value;
	}

	/** Modern: sun + shadow ray, AO, skylight, lantern, emissive blocks, then biome fog on top. */
	private void shadeModern() {
		// secondary rays overwrite the h* fields, so copy everything first
		final double hx = hHx, hy = hHy, hz = hHz, t = hT, cr = hR, cg = hG, cb = hB;
		final int axis = hAxis, sign = hSign, id = hId, q = lightQ;
		final long fx = hBx + (axis == 0 ? sign : 0), fy = hBy + (axis == 1 ? sign : 0), fz = hBz + (axis == 2 ? sign : 0);
		fog.at(hx, hy, hz);

		double sun = Math.max(0, sign * (axis == 0 ? lx : axis == 1 ? ly : lz));
		if (sun > 0.02) {
			double nx = axis == 0 ? sign : 0, ny = axis == 1 ? sign : 0, nz = axis == 2 ? sign : 0;
			if (march(hx + nx * EPS, hy + ny * EPS, hz + nz * EPS, lx, ly, lz, shadowDist, false, false))
				sun = 0;
		}
		double ao = 1, sky = 1;
		if (q >= 1) {
			double u = axis == 0 ? hy : hx, v = axis == 2 ? hy : hz;
			ao = 0.4 + 0.6 * aoAt(fx, fy, fz, axis, u - Math.floor(u), v - Math.floor(v));
		}
		if (q >= 2)
			sky = skyLight(fx, fy, fz);

		double amb = (0.1 + 0.9 * sky) * ao;
		double k = sun * 0.55 * (0.6 + 0.4 * ao);
		double lamp = q >= 2 ? (1 - sky) * Math.max(0, 1 - t / 18.0) * 0.7 : 0; // warm lantern carried by the player
		double lr = ambR * amb + sunR * k + lamp;
		double lg = ambG * amb + sunG * k + lamp * 0.8;
		double lb = ambB * amb + sunB * k + lamp * 0.5;
		double gl = GLOW[id];

		double ft = Math.min(1, t * fog.dens / maxDist);
		hR = cr * (lr + gl) * (1 - ft) + fog.r * ft;
		hG = cg * (lg + gl) * (1 - ft) + fog.g * ft;
		hB = cb * (lb + gl) * (1 - ft) + fog.b * ft;
	}
}

/** Fixed-capacity struct-of-arrays particle pool. Main thread only. World +y is down, so "up" is negative vy. */
final class Particles {
	static final int CAP = 32768;
	static final double GRAVITY = 0.002, DRAG = 0.995;
	static final double[] pX = new double[CAP], pY = new double[CAP], pZ = new double[CAP];
	static final double[] vX = new double[CAP], vY = new double[CAP], vZ = new double[CAP];
	static final float[] size = new float[CAP];
	static final int[] color = new int[CAP], life = new int[CAP];
	static int count, overwrite;
	static final Random R = new Random();

	static void clear() {
		count = 0;
	}

	static void spawn(double sx, double sy, double sz, double vx, double vy, double vz, int rgb, double sz2, int ttl) {
		int i;
		if (count < CAP) {
			i = count++;
		} else { // pool full: recycle slots round-robin
			i = overwrite;
			overwrite = (overwrite + 1) & (CAP - 1);
		}
		pX[i] = sx; pY[i] = sy; pZ[i] = sz;
		vX[i] = vx; vY[i] = vy; vZ[i] = vz;
		color[i] = rgb;
		size[i] = (float) sz2;
		life[i] = ttl;
	}

	/** A random opaque texel from the block's side face, slightly darkened/varied. */
	static int sample(int id) {
		for (int t = 0; t < 6; t++) {
			int c = atlas[R.nextInt(texRes) + (texRes + R.nextInt(texRes)) * texRes + id * TEX_STRIDE];
			if ((c & 0xFFFFFF) != 0) {
				double s = 0.7 + R.nextDouble() * 0.3;
				return (int) ((c >> 16 & 0xFF) * s) << 16 | (int) ((c >> 8 & 0xFF) * s) << 8 | (int) ((c & 0xFF) * s);
			}
		}
		return 0xB0C0D0;
	}

	/** Chips flying out of a broken block. */
	static void burst(long bx, long by, long bz, byte id, int n, double speed) {
		if (!particlesOn || id == AIR)
			return;
		for (int i = 0; i < n; i++)
			spawn(bx + R.nextDouble(), by + R.nextDouble(), bz + R.nextDouble(),
					(R.nextDouble() - 0.5) * speed, (R.nextDouble() - 0.8) * speed, (R.nextDouble() - 0.5) * speed,
					sample(id), 0.08 + R.nextDouble() * 0.08, 60 + R.nextInt(80));
	}

	private static double sprintDistance;

	/** Spawn a short, block-coloured dust trail while sprinting across solid ground. */
	static void sprintTrail(byte below, double moved) {
		if (!particlesOn || !Nexus.sprint || below == AIR || moved < 1e-4) {
			if (!Nexus.sprint || below == AIR)
				sprintDistance = 0;
			return;
		}
		sprintDistance += moved;
		if (sprintDistance < 0.22)
			return;
		sprintDistance %= 0.22;

		double dx = Nexus.x - Nexus.prevX, dz = Nexus.z - Nexus.prevZ;
		double len = Math.max(1e-6, Math.hypot(dx, dz));
		// A couple of tiny puffs per stride, kicked backwards and slightly upward.
		for (int n = 0; n < 2; n++) {
			double spreadX = (R.nextDouble() - 0.5) * 0.018;
			double spreadZ = (R.nextDouble() - 0.5) * 0.018;
			spawn(Nexus.x + (R.nextDouble() - 0.5) * 0.42,
				Nexus.y + 1.48 + R.nextDouble() * 0.05,
				Nexus.z + (R.nextDouble() - 0.5) * 0.42,
				-dx / len * (0.012 + R.nextDouble() * 0.012) + spreadX,
				-0.012 - R.nextDouble() * 0.012,
				-dz / len * (0.012 + R.nextDouble() * 0.012) + spreadZ,
				sample(below), 0.025 + R.nextDouble() * 0.035, 12 + R.nextInt(13));
		}
	}

	/** One chunk of debris (1 in 3 blocks) thrown away from an explosion centre. */
	static void debris(long bx, long by, long bz, byte id, double cx, double cy, double cz) {
		if (!particlesOn || id == AIR || R.nextInt(3) != 0)
			return;
		double ex = bx + 0.5, ey = by + 0.5, ez = bz + 0.5;
		double dx = ex - cx, dy = ey - cy, dz = ez - cz;
		double len = Math.sqrt(dx * dx + dy * dy + dz * dz) + 1e-6;
		double s = 0.03 + R.nextDouble() * 0.05;
		spawn(ex, ey, ez, dx / len * s, dy / len * s - 0.02, dz / len * s, sample(id), 0.1 + R.nextDouble() * 0.1, 80 + R.nextInt(100));
	}

	private static long qx = Long.MIN_VALUE, qy, qz;
	private static byte[] qc; // chunk cache, valid for one update() pass

	private static boolean solid(double x, double y, double z) {
		long bx = (long) Math.floor(x), by = (long) Math.floor(y), bz = (long) Math.floor(z);
		long cx = bx >> SHIFT, cy = by >> SHIFT, cz = bz >> SHIFT;
		if (cx != qx || cy != qy || cz != qz) {
			qx = cx; qy = cy; qz = cz;
			qc = world.chunk(cx, cy, cz);
		}
		byte[] c = qc;
		if (c == null || c == World.UNLOADED)
			return false;
		return c[(int) (bx & MASK) | ((int) (by & MASK) << SHIFT) | ((int) (bz & MASK) << 2 * SHIFT)] != AIR;
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
	}

	static void render() {
		if (!particlesOn || count == 0)
			return;
		final int[] out = Render.out;
		final float[] depth = Render.depth;
		final int w = Render.w, h = Render.h;
		final double syw = sinYaw, cyw = cosYaw, sp = sinPitch, cp = cosPitch;
		final double invXS = 1.0 / Render.xScale, invYS = 1.0 / Render.yScale;
		final double maxK = dist; // beyond the fog distance nothing is visible anyway
		for (int i = 0; i < count; i++) {
			double rx = pX[i] - Render.px, ry = pY[i] - Render.py, rz = pZ[i] - Render.pz;
			double zc = rz * cyw + rx * syw, xc = rx * cyw - rz * syw;
			double k = zc * cp - ry * sp;
			if (k < 0.1 || k > maxK)
				continue;
			double scrX = xc / k * invXS + w * 0.5;
			double scrY = (ry * cp + zc * sp) / k * invYS + h * 0.5;
			double half = size[i] * Math.min(1.0, life[i] / 20.0) * 0.5 / k;
			int hx = Math.min(12, (int) Math.round(half * invXS));
			int hy = Math.min(12, (int) Math.round(half * invYS));
			int cx = (int) Math.floor(scrX), cy = (int) Math.floor(scrY);
			if (cx + hx < 0 || cx - hx >= w || cy + hy < 0 || cy - hy >= h)
				continue; // off-screen: skip before the sqrt
			int x0 = Math.max(0, cx - hx), x1 = Math.min(w - 1, cx + hx);
			int y0 = Math.max(0, cy - hy), y1 = Math.min(h - 1, cy + hy);
			float d = (float) Math.sqrt(rx * rx + ry * ry + rz * rz);
			int col = color[i];
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
	private static final int N = 512;
	// rgb + density: none, moss, snow, obsidian, crystal (indexed by CB_*)
	private static final double[][] CAVE = {
		{ .03, .04, .06, 2.4 }, { .10, .34, .14, 2.0 }, { .45, .65, .90, 1.6 }, { .17, .06, .28, 2.4 }, { .03, .04, .06, 2.4 } };
	private static final int[] ASC = { CB_MOSS, CB_SNOW, CB_OBSIDIAN, CB_CRYSTAL }; // ascending priority
	private final long[] keys = new long[N];
	private final double[][] cache = new double[N][4];
	private double sr, sg, sb, sd;
	// Per-renderer cache of biome-noise lattice samples. Interpolation keeps the
	// tint continuous while avoiding a full noise evaluation for every pixel.
	private static final int BIOME_CACHE_SIZE = 1024;
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

	/** Evaluate a smoothly interpolated biome tint. No per-16x16 flat colour blocks. */
	private void surface(double wx, double wz) {
		double gx = Math.floor(wx / 16.0), gz = Math.floor(wz / 16.0);
		double fx = wx / 16.0 - gx, fz = wz / 16.0 - gz;
		// Hermite easing keeps both tint and its slope from popping at lattice edges.
		fx = fx * fx * (3 - 2 * fx);
		fz = fz * fz * (3 - 2 * fz);
		long ix = (long) gx, iz = (long) gz;
		double a = biomeSample(ix, iz), b = biomeSample(ix + 1, iz);
		double c = biomeSample(ix, iz + 1), d = biomeSample(ix + 1, iz + 1);
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

	private double[] cave(long x, long y, long z) {
		// Cache at 1x1x1 world-voxel resolution instead of 8x8x8. This removes
		// visible blocky fog boundaries while still reusing samples for pixels
		// that look through the same voxel.
		long k = World.key(x, y, z);
		int i = (int) ((k * 0x9E3779B97F4A7C15L) >>> 55);
		double[] c = cache[i];
		if (keys[i] != k) {
			keys[i] = k;
			System.arraycopy(CAVE[0], 0, c, 0, 4);
			for (int b : ASC) {
				double w = Nexus.zone(b, x, y, z);
				if (w > 0)
					for (int j = 0; j < 4; j++)
						c[j] += (CAVE[b][j] - c[j]) * w;
			}
			// Feather basin fog smoothly into nearby cave fog, evaluated per voxel
			// so the edge is not quantized into 8x8x8 blocks.
			int basinBiome = Nexus.basinFogBiome(x, y, z);
			if (basinBiome != CB_NONE) {
				double w = Nexus.basinFogWeight(x, y, z);
				for (int j = 0; j < 4; j++)
					c[j] += (CAVE[basinBiome][j] - c[j]) * w;
			}
		}
		return c;
	}

	/** Fog colour and density at a world position. */
	void at(double wx, double wy, double wz) {
		surface(wx, wz);
		r = sr * Render.fLR; g = sg * Render.fLG; b = sb * Render.fLB; dens = sd;
		double c = Render.cave;
		if (c > 0.002) {
			double[] k = cave((long) Math.floor(wx), (long) Math.floor(wy), (long) Math.floor(wz));
			r += (k[0] - r) * c; g += (k[1] - g) * c; b += (k[2] - b) * c; dens += (k[3] - dens) * c;
		}
	}
}
