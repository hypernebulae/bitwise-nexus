package bitwise;

import org.lwjgl.glfw.*;
import org.lwjgl.opengl.*;
import java.nio.*;
import java.util.*;
import java.awt.Color;
import java.awt.Font;
import java.awt.Graphics2D;
import java.awt.RenderingHints;
import java.awt.image.BufferedImage;
import java.awt.image.DataBufferInt;
import java.util.concurrent.*;
import java.text.DecimalFormat;
import java.text.DecimalFormatSymbols;
import static org.lwjgl.glfw.GLFW.*;
import static org.lwjgl.opengl.GL11.*;
import static org.lwjgl.opengl.GL12.*;
import static org.lwjgl.opengl.GL13.*;
import static org.lwjgl.opengl.GL15.*;
import static org.lwjgl.opengl.GL20.*;
import static org.lwjgl.opengl.GL30.*;
import static org.lwjgl.system.MemoryUtil.*;

/**
 * LWJGL 3 front end using Nexus' real terrain generator and procedural 36-block texture atlas.
 * Java 8 compatible. The world cache is streamed around the player and chunks are greedily meshed
 * off-thread; OpenGL resources are only touched on the context thread.
 */
public final class NexusLwjgl {
    private static final int CHUNK = Nexus.SIZE;
    private int renderDistance = 4;
    private float fovDegrees = 75f;
    private int draggingSlider = -1;
    private static final int VERTICAL_RADIUS = 2;
    private static final int ATLAS_H = Nexus.BLOCK_COUNT * 3 * Nexus.texRes;
    private long window;
    private int width=1280, height=800, program, atlasTexture, particleProgram, particleVao, particleVbo, uiProgram, uiTexture, uiVao, uiVbo;
    private ByteBuffer uiUpload; private boolean uiNeedsRedraw=true; private long lastUiDrawNanos=0; private boolean teleportOpen=false; private int teleportField=0; private final String[] teleportValues={"0.5","0","0.5","1.0"};
    private int locProjection,locView,locSunColor,locAmbientColor,locDaylight,locCameraPos,locFogColor,locFogDensity,locFogDistance,locClassic,locAtlas,locChunkOrigin;
    private boolean quitConfirm=false, qWasDown=false, eWasDown=false, spaceWasDown=false; private int fps=0, fpsFrames=0; private long fpsWindow=System.nanoTime();
    private final Fog worldFog = new Fog(); private float fogR=.32f, fogG=.5f, fogB=.68f, fogDensity=1f;
    private BufferedImage uiImage; private int[] uiPixels; private final Map<Byte,BufferedImage> blockIcons=new HashMap<>(); private boolean paused=false, settingsOpen=false, helpOpen=false, hWasDown=false; private double cursorX,cursorY; private long lastStepSound=0; private double lastStepX,lastStepZ;
    private double px=.5, py=0, pz=.5, vy=0;
    private double flightSpeed=12.0;
    private static final double MAX_FLIGHT_SPEED=100.0;
    private double mouseSensitivity=1.0;   // multiplier on the base .0025 rad/pixel
    private boolean wireframe=false;
    private boolean sprinting=false;
    // Second-level chunk store: chunks pushed out of Nexus.world (or out of range) are kept here and restored instead of regenerated.
    private final LinkedHashMap<Long,byte[]> chunkStore=new LinkedHashMap<>(256,.75f,true); // access-ordered = LRU
    private long chunkStoreBytes=0;
    private static final long CHUNK_STORE_BUDGET=48L<<20; // 48 MB; uniform (all air / all stone) chunks cost 1 byte
    // window / HUD
    private boolean fullscreen=false,f11WasDown=false,f3WasDown=false,hudText=true;
    private int winX=100,winY=100,winW=1280,winH=800;
    private float guiScale=1f,menuScale=1f;       // menuScale is frozen while the settings screen is open so dragging the GUI slider doesn't rescale under the cursor
    private int locUiTex=-1,streamTick=0;
    private final Set<Long> staleInFlight=ConcurrentHashMap.newKeySet(); // chunks edited by the player while a mesh job was already running
    private final List<GpuChunk> visibleChunks=new ArrayList<>();
    private static final byte[] ZERO_CHUNK=new byte[Nexus.VOL];
    private static final Font UI_BOLD16=new Font("Palatino Linotype",Font.BOLD,16);
    private static final Font UI_PLAIN16=new Font("Palatino Linotype",Font.PLAIN,16),UI_BOLD15=new Font("Palatino Linotype",Font.BOLD,15);
    private final Set<Long> knownEmpty=new HashSet<>();   // chunks whose mesh is legitimately empty (so they are not "missing")
    private int rebuildTick=0;
    // One scratch voxel volume per mesher thread instead of a fresh 287 KB array per mesh job.
    private static final ThreadLocal<byte[]> MESH_VOLUME=ThreadLocal.withInitial(()->new byte[66*66*66]);
    private static final DecimalFormat COORD_FORMAT=new DecimalFormat("0.###",DecimalFormatSymbols.getInstance(Locale.ROOT));
    private float yaw=0, pitch=0;
    private FloatBuffer particleData;
    private final List<GpuChunk> transparentOrder = new ArrayList<>();
    private boolean flyMode=false, grounded=false, autoGroundPending=false;
    private byte selectedBlock=Nexus.GRASS;
    private boolean leftWasDown=false, rightWasDown=false;
    private double lastX,lastY;
    private boolean firstMouse=true;
    private final boolean[] keys=new boolean[GLFW_KEY_LAST+1];
    private final ExecutorService generator=Executors.newFixedThreadPool(Math.max(1,Math.min(3,Runtime.getRuntime().availableProcessors()-2)),r->{Thread t=new Thread(r,"nexus-worldgen");t.setDaemon(true);return t;});
    private final ExecutorService mesher=Executors.newFixedThreadPool(Math.max(1,Math.min(3,(Runtime.getRuntime().availableProcessors()-1)/2)),r->{Thread t=new Thread(r,"nexus-greedy-mesher");t.setDaemon(true);return t;});
    private final ConcurrentLinkedQueue<GeneratedChunk> generated=new ConcurrentLinkedQueue<>();
    private final ConcurrentLinkedQueue<MeshResult> meshed=new ConcurrentLinkedQueue<>();
    private final Set<Long> requested=ConcurrentHashMap.newKeySet();
    private final Set<Long> meshRequested=ConcurrentHashMap.newKeySet();
    // If a chunk changes while its mesh job is running, remember to rebuild it after that result lands.
    private final Set<Long> meshAgain=ConcurrentHashMap.newKeySet();
    private final Map<Long,GpuChunk> gpuChunks=new HashMap<>();
    private volatile int worldEpoch=0, worldRevision=0;
    private long lastCenterKey=Long.MIN_VALUE;

    public static void main(String[] args){try{new NexusLwjgl().run();}finally{System.exit(0);}} // non-daemon leftovers (audio, AWT) can otherwise keep the JVM alive after the window closes

    private void run(){
        Nexus.radius=(short)renderDistance;
        Nexus.world.resize(renderDistance);
        Nexus.lwjglInitTextures();
        Nexus.lwjglUpdateHotbar();
        // Randomize horizontal spawn across the requested range, centered inside the chosen block.
        java.util.concurrent.ThreadLocalRandom spawnRng=java.util.concurrent.ThreadLocalRandom.current();
        long spawnX=spawnRng.nextInt(-4096,4097), spawnZ=spawnRng.nextInt(-4096,4097);
        px=spawnX+0.5; pz=spawnZ+0.5;
        // Use Nexus's original surface estimator at the actual spawn coordinates.
        py=Nexus.estimateGround(spawnX,spawnZ)-0.1;
        syncNexusPlayer();
        try { Nexus.init(); } catch (Throwable audioError) { System.err.println("Nexus audio initialization failed: " + audioError); }
        if(!glfwInit())throw new IllegalStateException("Unable to initialize GLFW");
        try{
            glfwDefaultWindowHints();glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR,3);glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR,2);
            glfwWindowHint(GLFW_OPENGL_PROFILE,GLFW_OPENGL_CORE_PROFILE);glfwWindowHint(GLFW_OPENGL_FORWARD_COMPAT,GLFW_TRUE);
            window=glfwCreateWindow(width,height,"Bitwise Nexus 3.0-alpha",NULL,NULL);
            if(window==NULL)throw new IllegalStateException("Unable to create GLFW window");
            glfwSetFramebufferSizeCallback(window,(w,a,b)->{width=Math.max(1,a);height=Math.max(1,b);glViewport(0,0,width,height);});
            glfwSetKeyCallback(window,(w,key,scan,action,mods)->{if(key>=0&&key<keys.length)keys[key]=action!=GLFW_RELEASE;if(action==GLFW_PRESS&&teleportOpen){uiNeedsRedraw=true;if(key==GLFW_KEY_BACKSPACE){String v=teleportValues[teleportField];if(!v.isEmpty())teleportValues[teleportField]=v.substring(0,v.length()-1);}else if(key==GLFW_KEY_TAB)teleportField=(teleportField+1)%3;else if(key==GLFW_KEY_ENTER)applyTeleport();else if(key==GLFW_KEY_ESCAPE)teleportOpen=false;}});
            glfwSetCharCallback(window,(w,cp)->{if(teleportOpen&&teleportField<3&&(Character.isDigit(cp)||cp=='-'||cp=='+'||cp=='.'||cp=='e'||cp=='E')){uiNeedsRedraw=true;String v=teleportValues[teleportField];if(v.length()<32)teleportValues[teleportField]=v+(char)cp;}});
            glfwSetCursorPosCallback(window,(w,x,y)->{cursorX=x;cursorY=y;if(paused){lastX=x;lastY=y;if(draggingSlider>=0){double mx=x*width/Math.max(1,windowWidth()),my=y*height/Math.max(1,windowHeight());updateSlider(draggingSlider,mx/uiScale(),my/uiScale());uiNeedsRedraw=true;}return;}if(firstMouse){lastX=x;lastY=y;firstMouse=false;}double dx=x-lastX,dy=y-lastY;lastX=x;lastY=y;float sens=.0025f*(float)mouseSensitivity;yaw+=(float)dx*sens;pitch-=(float)dy*sens;pitch=Math.max(-1.56905f,Math.min(1.56905f,pitch));});
            glfwSetMouseButtonCallback(window,(w,button,action,mods)->{if(button==GLFW_MOUSE_BUTTON_LEFT&&action==GLFW_RELEASE){draggingSlider=-1;}if(action==GLFW_PRESS){if(paused){int[] ww={1},wh={1};glfwGetWindowSize(window,ww,wh);double mx=cursorX*width/Math.max(1,ww[0]),my=cursorY*height/Math.max(1,wh[0]);handleUiClick(mx,my);uiNeedsRedraw=true;return;}if(button==GLFW_MOUSE_BUTTON_LEFT)breakTargetBlock();else if(button==GLFW_MOUSE_BUTTON_RIGHT)placeTargetBlock();else if(button==GLFW_MOUSE_BUTTON_MIDDLE)pickTargetBlock();}});
            glfwSetScrollCallback(window,(w,xoff,yoff)->{if(!paused&&yoff!=0){int n=Nexus.hotbar==null?9:Nexus.hotbar.length;Nexus.heldBlock=(byte)Math.floorMod(Nexus.heldBlock+(yoff<0?1:-1),Math.max(1,Math.min(9,n)));selectedBlock=currentHotbarBlock();}});
            glfwSetInputMode(window,GLFW_CURSOR,GLFW_CURSOR_DISABLED);glfwMakeContextCurrent(window);GL.createCapabilities();glfwSwapInterval(0); // Avoid VSync half-refresh locking (e.g. a hard 32 FPS on a 64 Hz display).
            glEnable(GL_DEPTH_TEST);glDisable(GL_CULL_FACE);glDisable(GL_DITHER);glEnable(GL_BLEND);glBlendFunc(GL_SRC_ALPHA,GL_ONE_MINUS_SRC_ALPHA);glEnable(0x8642); // GL_PROGRAM_POINT_SIZE (GL 3.2; numeric enum avoids LWJGL alias differences)
            program=createProgram();cacheWorldUniforms();atlasTexture=uploadAtlas();particleProgram=createParticleProgram();initParticleBuffers();particleData=memAllocFloat(Particles.CAP*7);initUi();glUseProgram(program);glUniform1i(locAtlas,0);
            glfwShowWindow(window);glfwSwapInterval(0);
            // Start the FPS window only after context/window initialization has settled.
            resetFpsSample();
            long prev=System.nanoTime();
            while(!glfwWindowShouldClose(window)){
                long now=System.nanoTime();float dt=Math.min(.05f,(now-prev)/1_000_000_000f);prev=now;glfwPollEvents();
                if(keys[GLFW_KEY_ESCAPE]){keys[GLFW_KEY_ESCAPE]=false;uiNeedsRedraw=true;if(teleportOpen){teleportOpen=false;}else if(quitConfirm){quitConfirm=false;}else if(paused&&settingsOpen){settingsOpen=false;}else{paused=!paused;settingsOpen=false;firstMouse=true;glfwSetInputMode(window,GLFW_CURSOR,paused?GLFW_CURSOR_NORMAL:GLFW_CURSOR_DISABLED);clearCaches(paused);prev=System.nanoTime();}}
                handleWindowKeys();if(!paused)move(dt); syncNexusPlayer();
                applyGenerated();Nexus.lwjglProcessFeatures();queueDirtyMeshes();applyMeshes();streamWorld();rebuildMissingMeshes();pruneGpuChunks();updateNexusLighting(now);Particles.update();
                if(!paused){handleBlockSelection();playFootsteps(now);if(keys[GLFW_KEY_H]&&!hWasDown)helpOpen=!helpOpen;hWasDown=keys[GLFW_KEY_H];}
                fpsFrames++;if(now-fpsWindow>=500_000_000L){fps=(int)Math.round(fpsFrames*1_000_000_000.0/(now-fpsWindow));fpsFrames=0;fpsWindow=now;}
                glViewport(0,0,width,height);
                glClearColor((float)Nexus.skyColor.x,(float)Nexus.skyColor.y,(float)Nexus.skyColor.z,1f);glClear(GL_COLOR_BUFFER_BIT|GL_DEPTH_BUFFER_BIT);
                drawWorld();drawParticles();drawUI();glfwSwapBuffers(window);
            }
        }finally{
            startExitWatchdog();
            generator.shutdownNow();mesher.shutdownNow();
            try{Nexus.lwjglShutdownAudio();}catch(Throwable t){t.printStackTrace();}
            for(GpuChunk c:gpuChunks.values())c.destroy();
            if(atlasTexture!=0)glDeleteTextures(atlasTexture);if(program!=0)glDeleteProgram(program);if(particleProgram!=0)glDeleteProgram(particleProgram);if(particleVao!=0)glDeleteVertexArrays(particleVao);if(particleVbo!=0)glDeleteBuffers(particleVbo);if(uiTexture!=0)glDeleteTextures(uiTexture);if(uiProgram!=0)glDeleteProgram(uiProgram);if(uiVao!=0)glDeleteVertexArrays(uiVao);if(uiVbo!=0)glDeleteBuffers(uiVbo);if(particleData!=null)memFree(particleData);
            if(uiUpload!=null)memFree(uiUpload);if(window!=NULL)glfwDestroyWindow(window);glfwTerminate();
        }
    }

    private void move(float dt){
        if(!Nexus.world.has(Math.floorDiv((long)Math.floor(px),CHUNK),Math.floorDiv((long)Math.floor(py),CHUNK),Math.floorDiv((long)Math.floor(pz),CHUNK)))return;
        if(autoGroundPending){
            double ground=Nexus.groundY(px,pz);
            if(Double.isFinite(ground)){py=ground;vy=0;grounded=false;autoGroundPending=false;}
        }
        if(keys[GLFW_KEY_LEFT])yaw-=1.8f*dt;
        if(keys[GLFW_KEY_RIGHT])yaw+=1.8f*dt;
        if(keys[GLFW_KEY_UP])pitch=Math.min(1.56905f,pitch+1.5f*dt);
        if(keys[GLFW_KEY_DOWN])pitch=Math.max(-1.56905f,pitch-1.5f*dt);
        boolean jumpPressed=keys[GLFW_KEY_SPACE]; // held = auto-jump the moment you land (no release needed)
        byte below=Nexus.getBlock((long)Math.floor(px),(long)Math.floor(py+1.7),(long)Math.floor(pz));
        // Sprint latches: tap/hold Ctrl while moving to start, it stays on until every movement key is released.
        boolean moving=keys[GLFW_KEY_W]||keys[GLFW_KEY_A]||keys[GLFW_KEY_S]||keys[GLFW_KEY_D]||(flyMode&&(keys[GLFW_KEY_SPACE]||keys[GLFW_KEY_LEFT_SHIFT]||keys[GLFW_KEY_RIGHT_SHIFT]));
        if(moving&&(keys[GLFW_KEY_LEFT_CONTROL]||keys[GLFW_KEY_RIGHT_CONTROL]))sprinting=true;
        if(!moving)sprinting=false;
        double speed=(flyMode?flightSpeed:6.0)*(sprinting?14.0/6.0:1.0)*dt;
        if(below==Nexus.ICE) speed*=1.75; // the original ice material increases horizontal momentum
        if(flyMode)speed=Math.min(speed,MAX_FLIGHT_SPEED*dt); // hard cap: 100 blocks/s even with sprint/ice
        double fx=Math.sin(yaw),fz=-Math.cos(yaw);
        double dx=0,dz=0;
        if(keys[GLFW_KEY_W]){dx+=fx*speed;dz+=fz*speed;}if(keys[GLFW_KEY_S]){dx-=fx*speed;dz-=fz*speed;}
        if(keys[GLFW_KEY_A]){dx-=Math.cos(yaw)*speed;dz-=Math.sin(yaw)*speed;}if(keys[GLFW_KEY_D]){dx+=Math.cos(yaw)*speed;dz+=Math.sin(yaw)*speed;}
        if(flyMode){
            if(keys[GLFW_KEY_SPACE])py-=speed;
            if(keys[GLFW_KEY_LEFT_SHIFT]||keys[GLFW_KEY_RIGHT_SHIFT])py+=speed;
            vy=0;
            // Flight should let the player escape solid blocks; collision checks can otherwise
            // trap the player when their starting position is already inside a block.
            px+=dx; pz+=dz; grounded=false;
        }
        else {
            if(jumpPressed&&grounded){vy=(below==Nexus.TOPAZ)?-18.0:-8.5;grounded=false;}
            vy=Math.min(18.0,vy+22.0*dt);
            moveAxis(dx,0,0);moveAxis(0,0,dz);moveAxis(0,vy*dt,0);
        }
    }

    private void moveAxis(double dx,double dy,double dz){
        double nx=px+dx,ny=py+dy,nz=pz+dz;
        if(!collides(nx,ny,nz)){px=nx;py=ny;pz=nz;}else if(dy>0){grounded=true;vy=0;}else if(dy<0){vy=0;}
    }
    // Camera is at eye height. Nexus uses +Y as down, so the body extends toward +Y.
    private boolean collides(double x,double eyeY,double z){
        double minX=x-.29,maxX=x+.29,minY=eyeY-.12,maxY=eyeY+1.62,minZ=z-.29,maxZ=z+.29;
        for(long bx=(long)Math.floor(minX);bx<=(long)Math.floor(maxX-1e-6);bx++)
            for(long by=(long)Math.floor(minY);by<=(long)Math.floor(maxY-1e-6);by++)
                for(long bz=(long)Math.floor(minZ);bz<=(long)Math.floor(maxZ-1e-6);bz++)
                    if(Nexus.getBlock(bx,by,bz)!=Nexus.AIR)return true;
        return false;
    }

    // ---- chunk store ----
    /** Called right before a chunk is written into Nexus.world: if its slot currently holds a different chunk, keep that one. */
    private void snapshotOccupant(long cx,long cy,long cz){
        int slot=Nexus.world.slot(cx,cy,cz);long old=Nexus.world.keys[slot];
        if(old==World.NONE||old==World.key(cx,cy,cz))return;
        long[] p=World.decodeKey(old);
        if(!Nexus.world.has(p[0],p[1],p[2]))return;
        byte[] d=Nexus.world.chunk(p[0],p[1],p[2]);
        if(d!=null)storeChunk(old,d);
    }
    private void snapshotWorldToStore(){
        for(int i=0;i<Nexus.world.keys.length;i++){long k=Nexus.world.keys[i];if(k==World.NONE)continue;long[] p=World.decodeKey(k);byte[] d=Nexus.world.chunk(p[0],p[1],p[2]);if(d!=null)storeChunk(k,d);}
    }
    private void storeChunk(long k,byte[] d){
        byte first=d[0];boolean uniform=true;for(int i=1;i<d.length;i++)if(d[i]!=first){uniform=false;break;}
        byte[] packed=uniform?new byte[]{first}:d.clone(); // clone: Nexus.world may reuse or overwrite its array
        byte[] prev=chunkStore.put(k,packed);if(prev!=null)chunkStoreBytes-=prev.length;
        chunkStoreBytes+=packed.length;
        Iterator<Map.Entry<Long,byte[]>> it=chunkStore.entrySet().iterator();
        while(chunkStoreBytes>CHUNK_STORE_BUDGET&&it.hasNext()){chunkStoreBytes-=it.next().getValue().length;it.remove();}
    }
    /** Puts a stored chunk back into the world (no generation, no feature re-run). Returns false if we don't have it. */
    private boolean restoreChunk(long cx,long cy,long cz,long k){
        if(requested.contains(k))return false;       // a generation job is already running for it
        byte[] p=chunkStore.remove(k);if(p==null)return false;
        chunkStoreBytes-=p.length;
        byte[] d=p;if(p.length!=Nexus.VOL){d=new byte[Nexus.VOL];if(p[0]!=0)Arrays.fill(d,p[0]);}
        snapshotOccupant(cx,cy,cz);Nexus.world.put(cx,cy,cz,d);
        queueMesh(cx,cy,cz);queueMesh(cx-1,cy,cz);queueMesh(cx+1,cy,cz);queueMesh(cx,cy-1,cz);queueMesh(cx,cy+1,cz);queueMesh(cx,cy,cz-1);queueMesh(cx,cy,cz+1);
        return true;
    }

    private void handleBlockSelection(){
        if(keys[GLFW_KEY_F]){keys[GLFW_KEY_F]=false;flyMode=!flyMode;vy=0;}
        if(keys[GLFW_KEY_Q]&&!qWasDown){Nexus.lwjglSelectPage(-1);blockIcons.clear();qWasDown=true;selectedBlock=currentHotbarBlock();}
        if(!keys[GLFW_KEY_Q])qWasDown=false;
        if(keys[GLFW_KEY_E]&&!eWasDown){Nexus.lwjglSelectPage(1);blockIcons.clear();eWasDown=true;selectedBlock=currentHotbarBlock();}
        if(!keys[GLFW_KEY_E])eWasDown=false;
        byte[] choices=Nexus.hotbar;
        for(int i=0;i<Math.min(9,choices.length);i++){int key=GLFW_KEY_1+i;if(keys[key]){keys[key]=false;Nexus.heldBlock=(byte)i;selectedBlock=choices[i];}}
        selectedBlock=currentHotbarBlock();
    }
    private byte currentHotbarBlock(){byte[] bar=Nexus.hotbar;if(bar==null||bar.length==0)return Nexus.GRASS;int i=Math.max(0,Math.min(bar.length-1,Nexus.heldBlock));return bar[i];}
    private void syncNexusPlayer(){Nexus.x=px;Nexus.y=py;Nexus.z=pz;Nexus.yaw=yaw;Nexus.pitch=pitch;}
    private void updateNexusLighting(long now){
        Nexus.time=now/10_000_000L;Nexus.light.y=Math.sin(-Nexus.time/6000.0);Nexus.light.z=Math.cos(-Nexus.time/6000.0);
        if(Nexus.light.y<0){Vec3.lerp(Nexus.SUN_LOW,Nexus.SUN_DAY,-Nexus.light.y,Nexus.sunColor);Vec3.lerp(Nexus.AMB_LOW,Nexus.AMB_DAY,-Nexus.light.y,Nexus.ambColor);Vec3.lerp(Nexus.SKY_LOW,Nexus.SKY_DAY,-Nexus.light.y,Nexus.skyColor);}
        else{Vec3.lerp(Nexus.SUN_LOW,Nexus.SUN_NIGHT,Nexus.light.y,Nexus.sunColor);Vec3.lerp(Nexus.AMB_LOW,Nexus.AMB_NIGHT,Nexus.light.y,Nexus.ambColor);Vec3.lerp(Nexus.SKY_LOW,Nexus.SKY_NIGHT,Nexus.light.y,Nexus.skyColor);}
        // Reuse the original biome/cave fog evaluator used by the Swing renderer.
        Render.cave=Nexus.caveMix;
        if(Nexus.classic){Render.fLR=Render.fLG=Render.fLB=1;}
        else {double lv=.12+.88*Nexus.daylight(),m=Math.max(1e-3,Math.max(Nexus.skyColor.x,Math.max(Nexus.skyColor.y,Nexus.skyColor.z)));Render.fLR=lv*(.65+.35*Nexus.skyColor.x/m);Render.fLG=lv*(.65+.35*Nexus.skyColor.y/m);Render.fLB=lv*(.65+.35*Nexus.skyColor.z/m);}
        worldFog.at(px,py,pz);fogR=(float)worldFog.r;fogG=(float)worldFog.g;fogB=(float)worldFog.b;fogDensity=(float)worldFog.dens;
    }
    private long[] rayTarget(){
        // Exact voxel DDA traversal avoids the visible jitter caused by fixed 0.05-unit ray steps.
        double dx=Math.sin(yaw)*Math.cos(pitch),dy=-Math.sin(pitch),dz=-Math.cos(yaw)*Math.cos(pitch);
        long x=(long)Math.floor(px),y=(long)Math.floor(py),z=(long)Math.floor(pz);
        int sx=dx>0?1:(dx<0?-1:0),sy=dy>0?1:(dy<0?-1:0),sz=dz>0?1:(dz<0?-1:0);
        double tx=dx==0?Double.POSITIVE_INFINITY:((dx>0?x+1-px:px-x)/Math.abs(dx));
        double ty=dy==0?Double.POSITIVE_INFINITY:((dy>0?y+1-py:py-y)/Math.abs(dy));
        double tz=dz==0?Double.POSITIVE_INFINITY:((dz>0?z+1-pz:pz-z)/Math.abs(dz));
        double dtx=dx==0?Double.POSITIVE_INFINITY:1/Math.abs(dx),dty=dy==0?Double.POSITIVE_INFINITY:1/Math.abs(dy),dtz=dz==0?Double.POSITIVE_INFINITY:1/Math.abs(dz);
        long pxCell=Long.MIN_VALUE,pyCell=Long.MIN_VALUE,pzCell=Long.MIN_VALUE;double t=0;
        for(int i=0;i<256&&t<=6.0;i++){
            byte block=Nexus.getBlock(x,y,z);
            if(block!=Nexus.AIR)return new long[]{x,y,z,pxCell,pyCell,pzCell};
            pxCell=x;pyCell=y;pzCell=z;
            if(tx<=ty&&tx<=tz){t=tx;tx+=dtx;x+=sx;}else if(ty<=tz){t=ty;ty+=dty;y+=sy;}else{t=tz;tz+=dtz;z+=sz;}
        }
        return null;
    }
    private void pickTargetBlock(){
        long[] hit=rayTarget(); if(hit==null)return;
        byte id=Nexus.getBlock(hit[0],hit[1],hit[2]); if(id==Nexus.AIR)return;
        Nexus.lwjglPickBlock(id); selectedBlock=currentHotbarBlock(); blockIcons.clear(); uiNeedsRedraw=true;
    }
    private void breakTargetBlock(){long[] hit=rayTarget();if(hit==null)return;byte id=Nexus.getBlock(hit[0],hit[1],hit[2]);if(id==Nexus.AIR)return;syncNexusPlayer();Particles.burst(hit[0],hit[1],hit[2],id,18,.09);Nexus.block(id,0,hit[0],hit[1],hit[2]);Nexus.setBlock(hit[0],hit[1],hit[2],Nexus.AIR);dirtyAround(hit[0],hit[1],hit[2]);}
    private void placeTargetBlock(){long[] hit=rayTarget();if(hit==null)return;byte target=Nexus.getBlock(hit[0],hit[1],hit[2]);if(target==Nexus.DYNAMITE||target==Nexus.EMERALD){Nexus.lwjglUseBlock(hit[0],hit[1],hit[2]);return;}if(hit[3]==Long.MIN_VALUE)return;long x=hit[3],y=hit[4],z=hit[5];if(Nexus.getBlock(x,y,z)!=Nexus.AIR)return;if(intersectsPlayer(x,y,z))return;syncNexusPlayer();Nexus.setBlock(x,y,z,selectedBlock);Nexus.block(selectedBlock,1,x,y,z);dirtyAround(x,y,z);}
    private boolean intersectsPlayer(long bx,long by,long bz){
        double minX=px-.29,maxX=px+.29,minY=py-.12,maxY=py+1.62,minZ=pz-.29,maxZ=pz+.29;
        return bx+1>minX&&bx<maxX&&by+1>minY&&by<maxY&&bz+1>minZ&&bz<maxZ;
    }
    private void dirtyAround(long x,long y,long z){
        // Only the edited chunk (and a neighbour if the block touches its border) can change. Mesh them NOW on this
        // thread instead of queueing behind every chunk that is still loading, so the block never "pops in" late.
        long cx=x>>Nexus.SHIFT,cy=y>>Nexus.SHIFT,cz=z>>Nexus.SHIFT,m=CHUNK-1,lx=x&m,ly=y&m,lz=z&m;
        meshImmediately(cx,cy,cz);
        if(lx==0)meshImmediately(cx-1,cy,cz);if(lx==m)meshImmediately(cx+1,cy,cz);
        if(ly==0)meshImmediately(cx,cy-1,cz);if(ly==m)meshImmediately(cx,cy+1,cz);
        if(lz==0)meshImmediately(cx,cy,cz-1);if(lz==m)meshImmediately(cx,cy,cz+1);
    }

    private void streamWorld(){
        long cx=floorDiv((long)Math.floor(px),CHUNK),cy=floorDiv((long)Math.floor(py),CHUNK),cz=floorDiv((long)Math.floor(pz),CHUNK);
        long center=World.key(cx,cy,cz);
        if(center!=lastCenterKey){lastCenterKey=center;worldEpoch++;}else if((++streamTick&3)!=0)return;
        final int epoch=worldRevision;
        List<long[]> missing=new ArrayList<>();
        for(int dx=-renderDistance;dx<=renderDistance;dx++)for(int dz=-renderDistance;dz<=renderDistance;dz++){
            if(dx*dx+dz*dz>renderDistance*renderDistance)continue;
            for(int dy=-VERTICAL_RADIUS;dy<=VERTICAL_RADIUS;dy++){
                long ax=cx+dx,ay=cy+dy,az=cz+dz,k=World.key(ax,ay,az);
                if(!Nexus.world.has(ax,ay,az)&&!restoreChunk(ax,ay,az,k)&&requested.add(k))missing.add(new long[]{ax,ay,az});
            }
        }
        missing.sort(Comparator.comparingLong(p->{long dx=p[0]-cx,dy=p[1]-cy,dz=p[2]-cz;return dx*dx+dy*dy+dz*dz;}));
        for(long[] p:missing)generator.submit(()->{byte[] d;
            try{d=Nexus.lwjglGenerateChunk(p[0],p[1],p[2]);}catch(Throwable ex){ex.printStackTrace();d=null;}
            generated.add(new GeneratedChunk(p[0],p[1],p[2],d,epoch));
        });
    }
    private static long floorDiv(long a,long b){return Math.floorDiv(a,b);}

    private void applyGenerated(){
        GeneratedChunk g;while((g=generated.poll())!=null){long cx=g.x,cy=g.y,cz=g.z;long k=World.key(cx,cy,cz);requested.remove(k);
            if(g.epoch!=worldRevision)continue;
            if(!nearPlayer(cx,cy,cz,renderDistance+1,VERTICAL_RADIUS+1))continue;
            snapshotOccupant(cx,cy,cz);Nexus.world.put(cx,cy,cz,g.data);
            Nexus.lwjglQueueFeatures(cx,cy,cz);
            queueMesh(cx,cy,cz);
            queueMesh(cx-1,cy,cz);queueMesh(cx+1,cy,cz);queueMesh(cx,cy-1,cz);queueMesh(cx,cy+1,cz);queueMesh(cx,cy,cz-1);queueMesh(cx,cy,cz+1);
        }
    }
    private boolean nearPlayer(long cx,long cy,long cz,int hr,int vr){long x=floorDiv((long)Math.floor(px),CHUNK),y=floorDiv((long)Math.floor(py),CHUNK),z=floorDiv((long)Math.floor(pz),CHUNK);long dx=cx-x,dy=cy-y,dz=cz-z;return dx*dx+dz*dz<=hr*hr&&Math.abs(dy)<=vr;}

    private void queueMesh(long cx,long cy,long cz){
        if(!Nexus.world.has(cx,cy,cz))return;
        long k=World.key(cx,cy,cz);
        if(!meshRequested.add(k)){meshAgain.add(k);return;}
        final int meshEpoch=worldRevision;
        mesher.submit(()->{
            try{
                MeshPair m=buildChunkMesh(cx,cy,cz);
                meshed.add(new MeshResult(cx,cy,cz,m,meshEpoch));
            }catch(Throwable ex){
                System.err.println("Failed to mesh chunk "+cx+","+cy+","+cz+": "+ex);
                meshRequested.remove(k);staleInFlight.remove(k); // rebuildMissingMeshes() will retry later
            }
        });
    }

    /** Builds the mesh for one chunk. Safe on any thread (per-thread scratch buffers). */
    private MeshPair buildChunkMesh(long cx,long cy,long cz){
        byte[] v=MESH_VOLUME.get();
        byte[] center=Nexus.world.chunk(cx,cy,cz);if(center==null)center=ZERO_CHUNK;
        final int S=Nexus.SHIFT;long bx=cx*CHUNK,by=cy*CHUNK,bz=cz*CHUNK;
        // interior: 4096 row copies instead of 262k single-byte copies
        for(int y=0;y<CHUNK;y++)for(int z=0;z<CHUNK;z++)System.arraycopy(center,(y<<S)|(z<<(2*S)),v,1+66*(z+1)+4356*(y+1),CHUNK);
        // the six 1-voxel border faces (edges/corners are never sampled by the mesher). Read neighbour arrays directly when loaded.
        int[] own=new int[3],nbp=new int[3];
        for(int d=0;d<3;d++)for(int s=-1;s<=1;s+=2){
            long nx=cx+(d==0?s:0),ny=cy+(d==1?s:0),nz=cz+(d==2?s:0);
            byte[] nb=Nexus.world.has(nx,ny,nz)?Nexus.world.chunk(nx,ny,nz):null;
            int d1=(d+1)%3,d2=(d+2)%3;own[d]=s<0?-1:CHUNK;nbp[d]=s<0?CHUNK-1:0;
            for(int a=0;a<CHUNK;a++)for(int b=0;b<CHUNK;b++){
                own[d1]=nbp[d1]=a;own[d2]=nbp[d2]=b;
                byte id=nb!=null?nb[nbp[0]|(nbp[1]<<S)|(nbp[2]<<(2*S))]:Nexus.getBlock(bx+own[0],by+own[1],bz+own[2]);
                v[(own[0]+1)+66*(own[2]+1)+4356*(own[1]+1)]=id;
            }
        }
        return GreedyMesher.build(v,bx,by,bz);
    }

    /** Main-thread mesh + upload, used for player edits. Any mesh job already in flight for this chunk is discarded when it lands. */
    private void meshImmediately(long cx,long cy,long cz){
        if(!Nexus.world.has(cx,cy,cz))return;
        long k=World.key(cx,cy,cz);
        if(meshRequested.contains(k))staleInFlight.add(k);
        MeshPair m;
        try{m=buildChunkMesh(cx,cy,cz);}catch(Throwable ex){ex.printStackTrace();queueMesh(cx,cy,cz);return;}
        GpuChunk old=gpuChunks.remove(k);if(old!=null)old.destroy();
        if(m.opaque.indices.remaining()>0||m.transparent.indices.remaining()>0){gpuChunks.put(k,uploadMesh(cx,cy,cz,m));knownEmpty.remove(k);}
        else{m.free();knownEmpty.add(k);}
        int slot=Nexus.world.slot(cx,cy,cz);if(Nexus.world.keys[slot]==k)Nexus.world.dirty[slot]=false;
    }

    private void applyMeshes(){
        long deadline=System.nanoTime()+4_000_000L; // upload budget (~4 ms/frame) so a burst of finished meshes can't hitch the frame
        MeshResult r;
        while((r=meshed.poll())!=null){
            long k=World.key(r.x,r.y,r.z);meshRequested.remove(k);
            if(staleInFlight.remove(k)){r.mesh.free();if(meshAgain.remove(k)&&Nexus.world.has(r.x,r.y,r.z))queueMesh(r.x,r.y,r.z);continue;} // an instant (player-edit) mesh already replaced it
            if(r.epoch!=worldRevision){r.mesh.free();if(meshAgain.remove(k)&&Nexus.world.has(r.x,r.y,r.z))queueMesh(r.x,r.y,r.z);continue;}
            if(!Nexus.world.has(r.x,r.y,r.z)||!nearPlayer(r.x,r.y,r.z,renderDistance+1,VERTICAL_RADIUS+1)){
                r.mesh.free();if(meshAgain.remove(k)&&Nexus.world.has(r.x,r.y,r.z))queueMesh(r.x,r.y,r.z);continue;
            }
            GpuChunk old=gpuChunks.remove(k);if(old!=null)old.destroy();
            if(r.mesh.opaque.indices.remaining()>0||r.mesh.transparent.indices.remaining()>0){gpuChunks.put(k,uploadMesh(r.x,r.y,r.z,r.mesh));knownEmpty.remove(k);}
            else{r.mesh.free();knownEmpty.add(k);} // remember "meshed, nothing to draw" so rebuildMissingMeshes() doesn't re-mesh it forever
            int slot=Nexus.world.slot(r.x,r.y,r.z);
            boolean dirty=Nexus.world.keys[slot]==k&&Nexus.world.dirty[slot];
            if(dirty)Nexus.world.dirty[slot]=false;
            // Rebuild after in-flight changes/neighbor arrivals so boundary faces and lighting cannot stay stale.
            boolean requestedAgain=meshAgain.remove(k);
            if(dirty||requestedAgain)queueMesh(r.x,r.y,r.z);
            if(System.nanoTime()>deadline)break;
        }
    }
    private void queueDirtyMeshes(){
        for(int i=0;i<Nexus.world.keys.length;i++)if(Nexus.world.dirty[i]&&Nexus.world.keys[i]!=World.NONE){long k=Nexus.world.keys[i];if(meshRequested.contains(k))continue;long[] p=World.decodeKey(k);Nexus.world.dirty[i]=false;queueMesh(p[0],p[1],p[2]);queueMesh(p[0]-1,p[1],p[2]);queueMesh(p[0]+1,p[1],p[2]);queueMesh(p[0],p[1]-1,p[2]);queueMesh(p[0],p[1]+1,p[2]);queueMesh(p[0],p[1],p[2]-1);queueMesh(p[0],p[1],p[2]+1);}
    }
    private void pruneGpuChunks(){Iterator<Map.Entry<Long,GpuChunk>> it=gpuChunks.entrySet().iterator();while(it.hasNext()){Map.Entry<Long,GpuChunk> e=it.next();GpuChunk c=e.getValue();if(!nearPlayer(c.x,c.y,c.z,renderDistance+1,VERTICAL_RADIUS+1)){c.destroy();it.remove();}}}

    private GpuChunk uploadMesh(long cx,long cy,long cz,MeshPair m){GpuMesh o=uploadOne(m.opaque),t=uploadOne(m.transparent);m.free();return new GpuChunk(cx,cy,cz,o.vao,o.vbo,o.ebo,o.count,t.vao,t.vbo,t.ebo,t.count);}
    private GpuMesh uploadOne(Mesh m){
        int count=m.indices.remaining();if(count==0)return new GpuMesh(0,0,0,0);
        int vao=glGenVertexArrays(),vbo=glGenBuffers(),ebo=glGenBuffers();
        glBindVertexArray(vao);
        glBindBuffer(GL_ARRAY_BUFFER,vbo);glBufferData(GL_ARRAY_BUFFER,m.vertices,GL_STATIC_DRAW);
        glBindBuffer(GL_ELEMENT_ARRAY_BUFFER,ebo);glBufferData(GL_ELEMENT_ARRAY_BUFFER,m.indices,GL_STATIC_DRAW);
        int stride=7*4; // x,y,z, u,v, tile, shade (the old 8th float, AO, was always 1.0)
        glVertexAttribPointer(0,3,GL_FLOAT,false,stride,0L);glEnableVertexAttribArray(0);
        glVertexAttribPointer(1,2,GL_FLOAT,false,stride,3L*4);glEnableVertexAttribArray(1);
        glVertexAttribPointer(2,1,GL_FLOAT,false,stride,5L*4);glEnableVertexAttribArray(2);
        glVertexAttribPointer(3,1,GL_FLOAT,false,stride,6L*4);glEnableVertexAttribArray(3);
        glBindVertexArray(0);
        return new GpuMesh(vao,vbo,ebo,count);
    }

    private void cacheWorldUniforms(){
        locProjection=glGetUniformLocation(program,"uProjection");locView=glGetUniformLocation(program,"uView");
        locSunColor=glGetUniformLocation(program,"uSunColor");locAmbientColor=glGetUniformLocation(program,"uAmbientColor");
        locDaylight=glGetUniformLocation(program,"uDaylight");locCameraPos=glGetUniformLocation(program,"uCameraPos");
        locFogColor=glGetUniformLocation(program,"uFogColor");locFogDensity=glGetUniformLocation(program,"uFogDensity");
        locFogDistance=glGetUniformLocation(program,"uFogDistance");locClassic=glGetUniformLocation(program,"uClassic");
        locAtlas=glGetUniformLocation(program,"uAtlas");locChunkOrigin=glGetUniformLocation(program,"uChunkOrigin");
    }

    private void drawChunks(){
        double ox=Math.floor(px/CHUNK)*CHUNK,oy=Math.floor(py/CHUNK)*CHUNK,oz=Math.floor(pz/CHUNK)*CHUNK;
        float[] projection=perspective((float)Math.toRadians(fovDegrees),width/(float)height,.05f,Math.max(1000f,renderDistance*CHUNK*2f));
        float fx=(float)(Math.sin(yaw)*Math.cos(pitch)),fy=(float)Math.sin(pitch),fz=(float)(-Math.cos(yaw)*Math.cos(pitch));
        float[] view=lookAt((float)(px-ox),(float)-(py-oy),(float)(pz-oz),(float)(px-ox)+fx,(float)-(py-oy)+fy,(float)(pz-oz)+fz,0,1,0);
        float[] frustum=extractFrustum(projection,view);
        glUseProgram(program);glUniformMatrix4fv(locProjection,false,projection);glUniformMatrix4fv(locView,false,view);glUniform3f(locSunColor,(float)(Nexus.sunColor.x*.65*Nexus.daylight()),(float)(Nexus.sunColor.y*.65*Nexus.daylight()),(float)(Nexus.sunColor.z*.65*Nexus.daylight()));glUniform3f(locAmbientColor,(float)(Nexus.ambColor.x*.72),(float)(Nexus.ambColor.y*.72),(float)(Nexus.ambColor.z*.72));glUniform1f(locDaylight,(float)Nexus.daylight());glUniform3f(locCameraPos,(float)(px-ox),(float)-(py-oy),(float)(pz-oz));glUniform3f(locFogColor,fogR,fogG,fogB);glUniform1f(locFogDensity,fogDensity);glUniform1f(locFogDistance,Math.max(32f,renderDistance*CHUNK*0.88f));glUniform1i(locClassic,Nexus.classic?1:0);glActiveTexture(GL_TEXTURE0);glBindTexture(GL_TEXTURE_2D,atlasTexture);
        glDepthMask(true);glDisable(GL_BLEND);
        visibleChunks.clear();for(GpuChunk c:gpuChunks.values()){if((c.opaqueCount==0&&c.transparentCount==0)||!chunkInFrustum(c,ox,oy,oz,frustum))continue;c.sortDistance=distanceToChunk(c,ox,oy,oz);visibleChunks.add(c);}
        visibleChunks.sort((a,b)->Double.compare(a.sortDistance,b.sortDistance)); // near to far: early-z for opaque; walked backwards for transparent
        for(GpuChunk c:visibleChunks){if(c.opaqueCount==0)continue;setChunkOrigin(c,ox,oy,oz);glBindVertexArray(c.opaqueVao);glDrawElements(GL_TRIANGLES,c.opaqueCount,GL_UNSIGNED_INT,0L);}
        glEnable(GL_BLEND);glBlendFunc(GL_SRC_ALPHA,GL_ONE_MINUS_SRC_ALPHA);glDepthMask(false);glDepthFunc(GL_LEQUAL);
        for(int i=visibleChunks.size()-1;i>=0;i--){GpuChunk c=visibleChunks.get(i);if(c.transparentCount==0)continue;setChunkOrigin(c,ox,oy,oz);glBindVertexArray(c.transparentVao);glDrawElements(GL_TRIANGLES,c.transparentCount,GL_UNSIGNED_INT,0L);}
        glBindVertexArray(0);glDepthMask(true);glDepthFunc(GL_LESS);glEnable(GL_BLEND);
    }
    // OpenGL clip-space frustum planes, extracted from projection * view.
    private static float[] extractFrustum(float[] projection,float[] view){
        float[] m=new float[16];
        for(int col=0;col<4;col++)for(int row=0;row<4;row++){
            float v=0;for(int k=0;k<4;k++)v+=projection[k*4+row]*view[col*4+k];m[col*4+row]=v;
        }
        float[] p=new float[24];int[][] signs={{1,0},{-1,0},{1,1},{-1,1},{1,2},{-1,2}};
        for(int i=0;i<6;i++){
            int row=signs[i][1];float sign=signs[i][0];
            float a=m[3]+sign*m[row],b=m[7]+sign*m[4+row],c=m[11]+sign*m[8+row],d=m[15]+sign*m[12+row];
            float len=(float)Math.sqrt(a*a+b*b+c*c);if(len>1e-6f){a/=len;b/=len;c/=len;d/=len;}
            p[i*4]=a;p[i*4+1]=b;p[i*4+2]=c;p[i*4+3]=d;
        }
        return p;
    }
    private static boolean chunkInFrustum(GpuChunk c,double ox,double oy,double oz,float[] planes){
        float x=(float)(c.x*CHUNK-ox+CHUNK*.5),y=(float)-(c.y*CHUNK-oy+CHUNK*.5),z=(float)(c.z*CHUNK-oz+CHUNK*.5);
        // Bounding sphere encloses the complete 64^3 chunk; conservative radius avoids edge popping.
        float radius=55.5f;
        for(int i=0;i<6;i++){int q=i*4;if(planes[q]*x+planes[q+1]*y+planes[q+2]*z+planes[q+3] < -radius)return false;}
        return true;
    }
    private double distanceToChunk(GpuChunk c,double ox,double oy,double oz){double x=c.x*CHUNK+CHUNK*.5-px,y=c.y*CHUNK+CHUNK*.5-py,z=c.z*CHUNK+CHUNK*.5-pz;return x*x+y*y+z*z;}
    private void setChunkOrigin(GpuChunk c,double ox,double oy,double oz){glUniform3f(locChunkOrigin,(float)(c.x*CHUNK-ox),(float)-(c.y*CHUNK-oy),(float)(c.z*CHUNK-oz));}

    private void initUi(){
        uiImage=new BufferedImage(width,height,BufferedImage.TYPE_INT_ARGB);uiPixels=((DataBufferInt)uiImage.getRaster().getDataBuffer()).getData();
        uiUpload=memAlloc(width*height*4);uiTexture=glGenTextures();glBindTexture(GL_TEXTURE_2D,uiTexture);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MIN_FILTER,GL_LINEAR);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MAG_FILTER,GL_LINEAR);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_WRAP_S,GL_CLAMP_TO_EDGE);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_WRAP_T,GL_CLAMP_TO_EDGE);glTexImage2D(GL_TEXTURE_2D,0,GL_RGBA8,width,height,0,GL_RGBA,GL_UNSIGNED_BYTE,(ByteBuffer)null);
        String vs="#version 150 core\nin vec2 aPos;in vec2 aUV;out vec2 vUV;void main(){vUV=aUV;gl_Position=vec4(aPos,0.0,1.0);}";
        String fs="#version 150 core\nin vec2 vUV;out vec4 fragColor;uniform sampler2D uUI;void main(){fragColor=texture(uUI,vUV);}";
        int v=shader(GL_VERTEX_SHADER,vs),f=shader(GL_FRAGMENT_SHADER,fs);uiProgram=glCreateProgram();glAttachShader(uiProgram,v);glAttachShader(uiProgram,f);glBindAttribLocation(uiProgram,0,"aPos");glBindAttribLocation(uiProgram,1,"aUV");glLinkProgram(uiProgram);if(glGetProgrami(uiProgram,GL_LINK_STATUS)==GL_FALSE)throw new IllegalStateException(glGetProgramInfoLog(uiProgram));glDeleteShader(v);glDeleteShader(f);
        float[] quad={-1,-1,0,1, 1,-1,1,1, 1,1,1,0, -1,-1,0,1, 1,1,1,0, -1,1,0,0};uiVao=glGenVertexArrays();uiVbo=glGenBuffers();glBindVertexArray(uiVao);glBindBuffer(GL_ARRAY_BUFFER,uiVbo);glBufferData(GL_ARRAY_BUFFER,quad,GL_STATIC_DRAW);glVertexAttribPointer(0,2,GL_FLOAT,false,4*4,0L);glEnableVertexAttribArray(0);glVertexAttribPointer(1,2,GL_FLOAT,false,4*4,2L*4);glEnableVertexAttribArray(1);glBindVertexArray(0);
    }
    private void drawUI(){
        if(uiImage==null||uiImage.getWidth()!=width||uiImage.getHeight()!=height){if(uiImage!=null)uiImage.flush();uiImage=new BufferedImage(Math.max(1,width),Math.max(1,height),BufferedImage.TYPE_INT_ARGB);uiPixels=((DataBufferInt)uiImage.getRaster().getDataBuffer()).getData();if(uiUpload!=null)memFree(uiUpload);uiUpload=memAlloc(width*height*4);glBindTexture(GL_TEXTURE_2D,uiTexture);glTexImage2D(GL_TEXTURE_2D,0,GL_RGBA8,width,height,0,GL_RGBA,GL_UNSIGNED_BYTE,(ByteBuffer)null);uiNeedsRedraw=true;}
        long uiNow=System.nanoTime();
        // Keep the projected block outline in sync with camera motion. Paused menus remain cached.
        if(!paused && uiNow-lastUiDrawNanos>=16_000_000L)uiNeedsRedraw=true;
        if(paused&&!uiNeedsRedraw){drawUiTexture();return;}
        if(!uiNeedsRedraw){drawUiTexture();return;}
        lastUiDrawNanos=uiNow;
        Arrays.fill(uiPixels,0);Graphics2D g=uiImage.createGraphics();g.setRenderingHint(RenderingHints.KEY_ANTIALIASING,RenderingHints.VALUE_ANTIALIAS_ON);
        final float guiS=uiScale();final int width=(int)Math.ceil(this.width/guiS),height=(int)Math.ceil(this.height/guiS);g.scale(guiS,guiS); // from here on, width/height in drawUI are GUI units
        Font uiFont=UI_PLAIN16;g.setFont(uiFont);
        if(!paused){
            int cx=width/2,cy=height/2;g.setColor(new Color(255,255,255,220));g.setStroke(new java.awt.BasicStroke(2f));g.drawLine(cx-8,cy,cx+8,cy);g.drawLine(cx,cy-8,cx,cy+8);
            // Restore the prior projected HUD outline instead of the newer depth-tested GL outline.
            {java.awt.geom.AffineTransform at=g.getTransform();g.setTransform(new java.awt.geom.AffineTransform());drawTargetOutline(g);g.setTransform(at);}
            if(hudText)drawHudText(g,uiFont); // F3 toggles this; hotbar and crosshair always stay
            int slot=40,gap=0,total=9*slot,x0=(width-total)/2,y0=height-slot-10;g.setColor(new Color(25,25,28,210));g.fillRect(x0-2,y0-2,total+4,slot+4);g.setColor(new Color(115,115,125));g.drawRect(x0-2,y0-2,total+4,slot+4);
            byte[] choices=Nexus.hotbar;
            for(int i=0;i<9;i++){int x=x0+i*(slot+gap);byte id=(choices!=null&&i<choices.length)?choices[i]:Nexus.AIR;BufferedImage icon=id==Nexus.AIR?null:blockIcon(id);if(icon!=null)g.drawImage(icon,x+4,y0+4,slot-8,slot-8,null);g.setColor(new Color(20,20,20,210));g.drawRect(x+3,y0+3,slot-6,slot-6);if(i==Nexus.heldBlock){g.setColor(Color.WHITE);g.setStroke(new java.awt.BasicStroke(3f));g.drawRect(x,y0,slot,slot);}}
            if(helpOpen){int w=440,h=270,x=(width-w)/2,y=(height-h)/2;g.setColor(new Color(18,18,20,235));g.fillRect(x,y,w,h);g.setColor(new Color(130,130,140));g.drawRect(x,y,w,h);g.setFont(new Font("Palatino Linotype",Font.BOLD,28));g.setColor(Color.WHITE);g.drawString("Controls",x+20,y+38);g.setFont(uiFont);String[] lines={"W A S D — Move     Mouse — Look","Space — Jump / fly up     Shift — fly down","Ctrl — Sprint     F — Toggle flight","Left click — Break     Right click — Place","1–9 — Select block     Q/E or wheel — Hotbar","Arrow keys — Rotate     Esc — Pause","F3 — Info text     F11 — Fullscreen","H — Hide this help"};for(int i=0;i<lines.length;i++)g.drawString(lines[i],x+20,y+72+i*27);}
        }else{
            g.setColor(new Color(18,18,20,220));g.fillRect(0,0,width,height);g.setFont(new Font("Palatino Linotype",Font.BOLD,Math.max(28,Math.min(42,width/24))));g.setColor(Color.WHITE);String title=settingsOpen?"Settings":"Paused!";int tw=g.getFontMetrics().stringWidth(title);g.drawString(title,(width-tw)/2,Math.max(70,height/5)+3);
            int x0=Math.max(24,width/2-210),w=Math.min(420,width-48),y0=Math.max(24,(height-560)/2);
            if(settingsOpen){
                drawSettingsPanel(g,x0,y0,w);
            }else if(quitConfirm){
                int bw=Math.min(360,Math.max(260,width-40)),bh=40,x=(width-bw)/2,y=height/2-50;
                g.setColor(new Color(5,5,8,245));g.fillRoundRect(x-24,y-60,bw+48,180,12,12);g.setColor(Color.WHITE);g.setFont(new Font("Palatino Linotype",Font.BOLD,20));String q="Quit Nexus?";g.drawString(q,(width-g.getFontMetrics().stringWidth(q))/2,y-22);
                uiButton(g,x,y,bw/2-5,bh,"Quit Game");uiButton(g,x+bw/2+5,y,bw/2-5,bh,"Cancel");
            }else if(teleportOpen){
                int dw=Math.min(440,width-40),dx=(width-dw)/2,dy=(height-310)/2;
                g.setColor(new Color(5,5,8,245));g.fillRoundRect(dx,dy,dw,310,12,12);g.setColor(Color.WHITE);g.setFont(new Font("Palatino Linotype",Font.BOLD,24));g.drawString("Teleport / World",dx+20,dy+34);
                String[] labels={"X", "Y", "Z"};
                for(int i=0;i<3;i++){int fy=dy+48+i*42;g.setFont(uiFont);g.setColor(new Color(215,215,220));g.drawString(labels[i],dx+18,fy+20);g.setColor(i==teleportField?new Color(70,90,120):new Color(38,40,46));g.fillRoundRect(dx+150,fy,dw-170,30,5,5);g.setColor(Color.WHITE);g.drawString(teleportValues[i]+(i==teleportField?"_":""),dx+160,fy+20);}
                int ampY=dy+174,ampX=dx+150,ampW=dw-170,gap=4,each=(ampW-gap*2)/3;
                g.setFont(uiFont);g.setColor(new Color(215,215,220));g.drawString("World amplitude",dx+18,ampY+20);
                uiButton(g,ampX,ampY,each,30,"Normal Amp.");uiButton(g,ampX+each+gap,ampY,each,30,"High Amp.");uiButton(g,ampX+2*(each+gap),ampY,ampW-2*(each+gap),30,"Ultra Amp.");
                uiButton(g,dx+18,dy+258,(dw-46)/2,34,"Apply");uiButton(g,dx+28+(dw-46)/2,dy+258,(dw-46)/2,34,"Cancel");
            }else{
                int bw=Math.min(360,Math.max(260,width-40)),bh=38,gap=10,count=5,top=Math.max(70,(height-(count*bh+(count-1)*gap))/2),x=(width-bw)/2;
                uiButton(g,x,top,bw,bh,"Return to Game");uiButton(g,x,top+bh+gap,bw,bh,"Settings");uiButton(g,x,top+2*(bh+gap),(bw-8)/2,bh,"Music: "+(Nexus.musicEnabled?"ON":"OFF"));uiButton(g,x+(bw-8)/2+8,top+2*(bh+gap),(bw-8)/2,bh,"Sounds: "+(Nexus.sound?"ON":"OFF"));uiButton(g,x,top+3*(bh+gap),bw,bh,"Teleport / World");uiButton(g,x,top+4*(bh+gap),bw,bh,"Quit Game");
            }
        }
        g.dispose();uploadUiPixels();uiNeedsRedraw=false;drawUiTexture();
    }
    private void drawUiTexture(){glDisable(GL_DEPTH_TEST);glDepthMask(false);glEnable(GL_BLEND);glBlendFunc(GL_SRC_ALPHA,GL_ONE_MINUS_SRC_ALPHA);glUseProgram(uiProgram);if(locUiTex<0)locUiTex=glGetUniformLocation(uiProgram,"uUI");glUniform1i(locUiTex,0);glActiveTexture(GL_TEXTURE0);glBindTexture(GL_TEXTURE_2D,uiTexture);glBindVertexArray(uiVao);glDrawArrays(GL_TRIANGLES,0,6);glBindVertexArray(0);glDepthMask(true);glEnable(GL_DEPTH_TEST);}

    private BufferedImage blockIcon(byte id){BufferedImage cached=blockIcons.get(id);if(cached!=null)return cached;int size=Nexus.texRes,y0=(id*3+1)*size;if(y0<0||y0+size> Nexus.atlas.length/size)return null;BufferedImage icon=new BufferedImage(size,size,BufferedImage.TYPE_INT_ARGB);for(int y=0;y<size;y++)for(int x=0;x<size;x++)icon.setRGB(x,y,Nexus.atlas[x+(y0+y)*size]);blockIcons.put(id,icon);return icon;}
    private void drawUiSlider(Graphics2D g,int x,int y,int w,String label,double t,String value){g.setFont(UI_BOLD15);g.setColor(Color.WHITE);g.drawString(label+": "+value,x,y+3);int sy=y+18;g.setColor(new Color(75,75,82));g.fillRoundRect(x,sy,w,8,8,8);int knob=x+(int)(Math.max(0,Math.min(1,t))*w);g.setColor(new Color(185,185,195));g.fillRect(knob-5,sy-3,10,14);}
    private void uiButton(Graphics2D g,int x,int y,int w,int h,String text){g.setColor(new Color(65,65,72,245));g.fillRoundRect(x,y,w,h,9,9);g.setColor(new Color(130,130,140,230));g.drawRoundRect(x,y,w,h,9,9);g.setColor(Color.WHITE);g.setFont(UI_BOLD15);java.awt.FontMetrics fm=g.getFontMetrics();int sw=fm.stringWidth(text);g.drawString(text,x+(w-sw)/2,y+(h+fm.getAscent()-fm.getDescent())/2+2);}
    private void drawTargetOutline(Graphics2D g){
        long[] hit=rayTarget();if(hit==null)return;
        double ox=Math.floor(px/CHUNK)*CHUNK,oy=Math.floor(py/CHUNK)*CHUNK,oz=Math.floor(pz/CHUNK)*CHUNK;
        float fx=(float)(Math.sin(yaw)*Math.cos(pitch)),fy=(float)Math.sin(pitch),fz=(float)(-Math.cos(yaw)*Math.cos(pitch));
        float[] view=lookAt((float)(px-ox),(float)-(py-oy),(float)(pz-oz),(float)(px-ox)+fx,(float)-(py-oy)+fy,(float)(pz-oz)+fz,0,1,0);
        float[] proj=perspective((float)Math.toRadians(fovDegrees),width/(float)height,.05f,Math.max(1000f,renderDistance*CHUNK*2f));
        double[][] points=new double[8][2];boolean[] valid=new boolean[8];
        for(int i=0;i<8;i++){double wx=hit[0]+((i&1)==0?0:1),wy=hit[1]+((i&2)==0?0:1),wz=hit[2]+((i&4)==0?0:1);double rx=wx-ox,ry=-(wy-oy),rz=wz-oz;
            double vx=view[0]*rx+view[4]*ry+view[8]*rz+view[12],vy=view[1]*rx+view[5]*ry+view[9]*rz+view[13],vz=view[2]*rx+view[6]*ry+view[10]*rz+view[14],vw=view[3]*rx+view[7]*ry+view[11]*rz+view[15];
            double cx=proj[0]*vx+proj[4]*vy+proj[8]*vz+proj[12]*vw,cy=proj[1]*vx+proj[5]*vy+proj[9]*vz+proj[13]*vw,cw=proj[3]*vx+proj[7]*vy+proj[11]*vz+proj[15]*vw;
            if(cw>0){points[i][0]=(cx/cw*.5+.5)*width;points[i][1]=(1-(cy/cw*.5+.5))*height;valid[i]=true;}}
        g.setColor(new Color(255,255,255,235));g.setStroke(new java.awt.BasicStroke(1.6f));int[][] edges={{0,1},{2,3},{4,5},{6,7},{0,2},{1,3},{4,6},{5,7},{0,4},{1,5},{2,6},{3,7}};
        for(int[] e:edges)if(valid[e[0]]&&valid[e[1]])g.drawLine((int)points[e[0]][0],(int)points[e[0]][1],(int)points[e[1]][0],(int)points[e[1]][1]);
    }

    private int windowWidth(){int[] a={1},b={1};glfwGetWindowSize(window,a,b);return a[0];}
    private int windowHeight(){int[] a={1},b={1};glfwGetWindowSize(window,a,b);return b[0];}
    private void updateSlider(int which,double mx,double my){
        final int width=uiLogicalW(); // mx is already in GUI units
        int x=Math.max(24,width/2-210),w=Math.min(420,width-48);double t=Math.max(0,Math.min(1,(mx-x)/(double)w));
        if(which==0)Nexus.soundVolume=2*t;
        else if(which==1)Nexus.musicVolume=2*t;
        else if(which==2)fovDegrees=(float)(50+60*t);
        else if(which==3){int old=renderDistance;renderDistance=2+(int)Math.round(10*t);if(old!=renderDistance){Nexus.radius=(short)renderDistance;snapshotWorldToStore();Nexus.world.resize(renderDistance);lastCenterKey=Long.MIN_VALUE;requested.clear();worldEpoch++;}}
        else if(which==4)flightSpeed=2.0+(MAX_FLIGHT_SPEED-2.0)*t;
        else if(which==5)mouseSensitivity=0.1+2.9*t;
        else if(which==6)guiScale=(float)(Math.round((0.75+2.25*t)*4)/4.0); // 0.75x to 3.00x in 0.25 steps
    }

    private static String format(double value, DecimalFormat f) { if (Math.abs(value) >= 1E10 || Double.isNaN(value)) return String.valueOf(value); return f.format(value); }
    private static String formatCoordinate(double value){
        String s=format(value,COORD_FORMAT);
        return s.equals("-0")?"0":s; // DecimalFormat prints -0.0 / tiny negatives as "-0"
    }

    private void resetWorldForAmplitude(double a){if(Math.abs(a-Nexus.amp)<=.0001)return;Nexus.lwjglSetAmplitude(a);autoGroundPending=true;worldRevision++;worldEpoch++;lastCenterKey=Long.MIN_VALUE;requested.clear();meshRequested.clear();meshAgain.clear();generated.clear();knownEmpty.clear();staleInFlight.clear();chunkStore.clear();chunkStoreBytes=0;MeshResult stale;while((stale=meshed.poll())!=null)stale.mesh.free();for(GpuChunk c:gpuChunks.values())c.destroy();gpuChunks.clear();}
    private void applyAmplitudePreset(double a){teleportValues[3]=Integer.toString((int)a);resetWorldForAmplitude(a);uiNeedsRedraw=true;}
    private void applyTeleport(){try{double x=Double.parseDouble(teleportValues[0]),y=Double.parseDouble(teleportValues[1]),z=Double.parseDouble(teleportValues[2]),a=Double.parseDouble(teleportValues[3]);if(!Double.isFinite(x)||!Double.isFinite(y)||!Double.isFinite(z)||!Double.isFinite(a)||a<0||a>100)return;px=x;py=-y;pz=z;vy=0;grounded=false;resetWorldForAmplitude(a);teleportOpen=false;uiNeedsRedraw=true;resetFpsSample();}catch(NumberFormatException ignored){}}

    // ===================== NEW METHODS =====================

    /** Wireframe wrapper: switch polygon mode only for the chunk pass; UI (also triangles) and particles stay filled. */
    private void drawWorld(){
        glPolygonMode(GL_FRONT_AND_BACK,wireframe?GL_LINE:GL_FILL);
        drawChunks();
        glPolygonMode(GL_FRONT_AND_BACK,GL_FILL);
    }

    /** Called on pause and on unpause. Drops CPU-side caches and far GPU chunks so the transition doesn't hitch. */
    private void clearCaches(boolean nowPaused){
        blockIcons.clear();                       // hotbar icons are re-rasterised lazily
        transparentOrder.clear();                 // sort list, rebuilt every frame anyway
        if(uiImage!=null)uiImage.flush();         // release cached Java2D surface state
        pruneGpuChunks();                         // free VAOs/VBOs that are out of range right now
        pruneKnownEmpty();
        uiNeedsRedraw=true;
        resetFpsSample();
        if(nowPaused)System.gc();                 // collect while the menu is up, so the hitch isn't felt after unpausing
    }

    private void pruneKnownEmpty(){
        knownEmpty.removeIf(k->{long[] c=World.decodeKey(k);return !nearPlayer(c[0],c[1],c[2],renderDistance+1,VERTICAL_RADIUS+1);});
    }

    /**
     * Safety net for "holes": any chunk that has block data, is in range, is not meshed/queued and isn't a known-empty
     * chunk gets re-queued. Visible (in-frustum) and nearby chunks only, nearest first, a few per pass.
     * Covers meshes dropped while out of range, failed jobs, and stale epochs.
     */
    private void rebuildMissingMeshes(){
        if((++rebuildTick&7)!=0)return;           // every 8th frame is plenty
        if((rebuildTick&63)==0)pruneKnownEmpty();
        final long cx=floorDiv((long)Math.floor(px),CHUNK),cy=floorDiv((long)Math.floor(py),CHUNK),cz=floorDiv((long)Math.floor(pz),CHUNK);
        double ox=Math.floor(px/CHUNK)*CHUNK,oy=Math.floor(py/CHUNK)*CHUNK,oz=Math.floor(pz/CHUNK)*CHUNK;
        float[] projection=perspective((float)Math.toRadians(fovDegrees),width/(float)height,.05f,Math.max(1000f,renderDistance*CHUNK*2f));
        float fx=(float)(Math.sin(yaw)*Math.cos(pitch)),fy=(float)Math.sin(pitch),fz=(float)(-Math.cos(yaw)*Math.cos(pitch));
        float[] view=lookAt((float)(px-ox),(float)-(py-oy),(float)(pz-oz),(float)(px-ox)+fx,(float)-(py-oy)+fy,(float)(pz-oz)+fz,0,1,0);
        float[] frustum=extractFrustum(projection,view);
        List<long[]> missing=new ArrayList<>();
        for(int dx=-renderDistance;dx<=renderDistance;dx++)for(int dz=-renderDistance;dz<=renderDistance;dz++){
            if(dx*dx+dz*dz>renderDistance*renderDistance)continue;
            for(int dy=-VERTICAL_RADIUS;dy<=VERTICAL_RADIUS;dy++){
                long ax=cx+dx,ay=cy+dy,az=cz+dz;
                if(!Nexus.world.has(ax,ay,az))continue;
                long k=World.key(ax,ay,az);
                if(gpuChunks.containsKey(k)||meshRequested.contains(k)||knownEmpty.contains(k))continue;
                boolean close=dx*dx+dz*dz<=4&&Math.abs(dy)<=1;
                if(!close&&!chunkCenterInFrustum(ax,ay,az,ox,oy,oz,frustum))continue;
                missing.add(new long[]{ax,ay,az});
            }
        }
        if(missing.isEmpty())return;
        missing.sort(Comparator.comparingLong(p->{long dx=p[0]-cx,dy=p[1]-cy,dz=p[2]-cz;return dx*dx+dy*dy+dz*dz;}));
        for(int i=0;i<Math.min(8,missing.size());i++){long[] p=missing.get(i);queueMesh(p[0],p[1],p[2]);}
    }
    private static boolean chunkCenterInFrustum(long cx,long cy,long cz,double ox,double oy,double oz,float[] planes){
        float x=(float)(cx*CHUNK-ox+CHUNK*.5),y=(float)-(cy*CHUNK-oy+CHUNK*.5),z=(float)(cz*CHUNK-oz+CHUNK*.5);
        for(int i=0;i<6;i++){int q=i*4;if(planes[q]*x+planes[q+1]*y+planes[q+2]*z+planes[q+3]< -55.5f)return false;}
        return true;
    }

    // ---- settings panel (layout offsets are relative to settingsTop(), in GUI units) ----
    // sliders: 0 sound, 52 music, 104 fov, 156 render dist, 372 flight, 424 sensitivity, 476 GUI scale
    // buttons: 214 sounds/music, 252 classic, 290 xor, 328 wireframe, 520 apply & close
    private static final int[] SLIDER_Y={0,52,104,156,372,424,476};
    private int settingsTop(){return Math.max(24,(uiLogicalH()-560)/2);}

    private void drawSettingsPanel(Graphics2D g,int x0,int y0,int w){
        drawUiSlider(g,x0,y0,w,"Sound volume",Nexus.soundVolume/2.0,Math.round(Nexus.soundVolume*100)+"%");
        drawUiSlider(g,x0,y0+52,w,"Music volume",Nexus.musicVolume/2.0,Math.round(Nexus.musicVolume*100)+"%");
        drawUiSlider(g,x0,y0+104,w,"Field of view",(fovDegrees-50f)/60f,Math.round(fovDegrees)+"°");
        drawUiSlider(g,x0,y0+156,w,"Render distance",(renderDistance-2)/10.0,renderDistance+" chunks");
        int half=(w-10)/2;
        uiButton(g,x0,y0+214,half,32,"Sounds: "+(Nexus.sound?"ON":"OFF"));uiButton(g,x0+half+10,y0+214,half,32,"Music: "+(Nexus.musicEnabled?"ON":"OFF"));
        uiButton(g,x0,y0+252,w,32,"Classic Mode: "+(Nexus.classic?"ON":"OFF"));
        uiButton(g,x0,y0+290,w,32,"XOR Texture Mode: "+(Nexus.xor?"ON":"OFF"));
        uiButton(g,x0,y0+328,w,32,"Wireframe: "+(wireframe?"ON":"OFF"));
        drawUiSlider(g,x0,y0+372,w,"Flight speed",(flightSpeed-2.0)/(MAX_FLIGHT_SPEED-2.0),String.format(Locale.ROOT,"%.1f blocks/s",flightSpeed));
        drawUiSlider(g,x0,y0+424,w,"Mouse sensitivity",(mouseSensitivity-.1)/2.9,String.format(Locale.ROOT,"%.2fx",mouseSensitivity));
        drawUiSlider(g,x0,y0+476,w,"GUI scale",(guiScale-.75)/2.25,String.format(Locale.ROOT,"%.2fx",guiScale));
        uiButton(g,x0,y0+520,w,36,"Apply & Close");
    }

    private void handleSettingsClick(double mx,double my){
        final int width=uiLogicalW();
        int x=Math.max(24,width/2-210),w=Math.min(420,width-48),y=settingsTop(),half=(w-10)/2;
        for(int i=0;i<SLIDER_Y.length;i++){int sy=y+SLIDER_Y[i];if(my>=sy+10&&my<=sy+38){draggingSlider=i;updateSlider(i,mx,my);return;}}
        if(my>=y+214&&my<=y+246){if(mx<x+half)Nexus.sound=!Nexus.sound;else if(mx<x+w)Nexus.musicEnabled=!Nexus.musicEnabled;return;}
        if(my>=y+252&&my<=y+284){Nexus.lwjglSetModes(!Nexus.classic,Nexus.xor);resetFpsSample();return;}
        if(my>=y+290&&my<=y+322){Nexus.lwjglSetModes(Nexus.classic,!Nexus.xor);blockIcons.clear();atlasTexture=reloadAtlasTexture();resetFpsSample();return;}
        if(my>=y+328&&my<=y+360){wireframe=!wireframe;return;}
        if(my>=y+520&&my<=y+556){settingsOpen=false;draggingSlider=-1;return;}
    }

    /** Bulk-uploads the Java2D ARGB pixels. BGRA + 8_8_8_8_REV is exactly the in-memory layout of TYPE_INT_ARGB on little-endian, so no per-pixel swizzle is needed. */
    private void uploadUiPixels(){
        IntBuffer ib=uiUpload.asIntBuffer();
        ib.clear();ib.put(uiPixels);ib.flip();
        glBindTexture(GL_TEXTURE_2D,uiTexture);glPixelStorei(GL_UNPACK_ALIGNMENT,1);
        glTexSubImage2D(GL_TEXTURE_2D,0,0,0,width,height,GL_BGRA,GL_UNSIGNED_INT_8_8_8_8_REV,ib);
    }

    /** If anything non-daemon (audio, AWT, ...) keeps the JVM alive after the window closes, force-exit after 3 s. */
    private void startExitWatchdog(){
        Thread t=new Thread(()->{try{Thread.sleep(3000);}catch(InterruptedException ignored){}Runtime.getRuntime().halt(0);},"nexus-exit-watchdog");
        t.setDaemon(true);t.start();
    }

    // ---- GUI scale ----
    private float computeUiScale(){float s=guiScale;if(paused)s=Math.min(s,Math.min(height/580f,width/460f));return Math.max(.5f,s);} // menus never scale past what fits the window
    private float uiScale(){return (paused&&settingsOpen)?menuScale:computeUiScale();}
    private int uiLogicalW(){return Math.max(1,(int)Math.ceil(width/uiScale()));}
    private int uiLogicalH(){return Math.max(1,(int)Math.ceil(height/uiScale()));}

    // ---- F11 / F3 ----
    private void handleWindowKeys(){
        if(keys[GLFW_KEY_F11]&&!f11WasDown)toggleFullscreen();f11WasDown=keys[GLFW_KEY_F11];
        if(keys[GLFW_KEY_F3]&&!f3WasDown){hudText=!hudText;uiNeedsRedraw=true;}f3WasDown=keys[GLFW_KEY_F3];
    }
    private void toggleFullscreen(){
        if(!fullscreen){
            int[] x={0},y={0},w={0},h={0};glfwGetWindowPos(window,x,y);glfwGetWindowSize(window,w,h);winX=x[0];winY=y[0];winW=w[0];winH=h[0];
            long monitor=glfwGetPrimaryMonitor();GLFWVidMode mode=monitor==NULL?null:glfwGetVideoMode(monitor);
            if(mode==null)return;
            glfwSetWindowMonitor(window,monitor,0,0,mode.width(),mode.height(),mode.refreshRate());fullscreen=true;
        }else{
            glfwSetWindowMonitor(window,NULL,winX,winY,winW,winH,GLFW_DONT_CARE);fullscreen=false;
        }
        glfwSwapInterval(0);firstMouse=true;uiNeedsRedraw=true;resetFpsSample(); // mode switches can reset VSync
    }

    private void drawHudText(Graphics2D g,Font f){
        int gy=22;g.setFont(UI_BOLD16);g.setColor(Color.RED);g.drawString(fps+" FPS",8,gy);gy+=23;
        g.setFont(f);
        g.setColor(Color.YELLOW);g.drawString("X: "+formatCoordinate(px),8,gy);gy+=19;g.drawString("Y: "+formatCoordinate(-py),8,gy);gy+=19;g.drawString("Z: "+formatCoordinate(pz),8,gy);gy+=19;
        g.setColor(Color.GREEN);
        g.drawString("Chunk: ("+Math.floorDiv((long)Math.floor(px),CHUNK)+", "+Math.floorDiv((long)Math.floor(-py),CHUNK)+", "+Math.floorDiv((long)Math.floor(pz),CHUNK)+")",8,gy);gy+=19;
        g.drawString("Index: ("+Math.floorMod((long)Math.floor(px),CHUNK)+", "+Math.floorMod((long)Math.floor(-py),CHUNK)+", "+Math.floorMod((long)Math.floor(pz),CHUNK)+")",8,gy);gy+=19;
        double yawDeg=((Math.toDegrees(yaw)%360)+360)%360,pitchDeg=Math.toDegrees(pitch);
        g.setColor(Color.CYAN);
        g.drawString(String.format(Locale.ROOT,"Rotation: (%.1f°, %.1f°)",yawDeg,pitchDeg),8,gy);gy+=19;
        g.drawString("FOV: "+Math.round(fovDegrees)+"°",8,gy);gy+=19;
        g.setColor(Color.MAGENTA);
        g.drawString("Window: "+width+"x"+height+(fullscreen?" (fullscreen)":""),8,gy);gy+=19;
        g.drawString("GUI Scale: "+String.format(Locale.ROOT,"%.2fx",guiScale),8,gy);
    }

    private void resetFpsSample(){fpsFrames=0;fpsWindow=System.nanoTime();}

    private void handleUiClick(double mx,double my){
        mx/=uiScale();my/=uiScale();final int width=uiLogicalW(),height=uiLogicalH(); // everything below works in GUI units
        if(teleportOpen){int dw=Math.min(440,width-40),dx=(width-dw)/2,dy=(height-310)/2;if(my>=dy+258&&my<=dy+292){int buttonW=(dw-46)/2;int applyX=dx+18;int cancelX=dx+28+buttonW;if(mx>=applyX&&mx<=applyX+buttonW)applyTeleport();else if(mx>=cancelX&&mx<=cancelX+buttonW)teleportOpen=false;return;}int ampY=dy+174,ampX=dx+150,ampW=dw-170,gap=4,each=(ampW-gap*2)/3;if(my>=ampY&&my<=ampY+30&&mx>=ampX&&mx<=ampX+ampW){if(mx<ampX+each)applyAmplitudePreset(1);else if(mx<ampX+2*(each+gap))applyAmplitudePreset(10);else applyAmplitudePreset(100);return;}for(int i=0;i<3;i++){int fy=dy+58+i*42;if(my>=fy&&my<=fy+30){teleportField=i;return;}}return;}
        if(quitConfirm){int bw=Math.min(360,Math.max(260,width-40)),bh=40,x=(width-bw)/2,y=height/2-50;if(my>=y&&my<=y+bh){if(mx<x+bw/2-5){glfwSetWindowShouldClose(window,true);}else{quitConfirm=false;}}return;}
        if(settingsOpen){handleSettingsClick(mx,my);return;}
        int bw=Math.min(360,Math.max(260,width-40)),bh=38,gap=10,count=5,top=Math.max(70,(height-(count*bh+(count-1)*gap))/2),x=(width-bw)/2;
        if(mx<x||mx>x+bw)return;
        if(my>=top&&my<top+bh){paused=false;firstMouse=true;glfwSetInputMode(window,GLFW_CURSOR,GLFW_CURSOR_DISABLED);clearCaches(false);return;}
        if(my>=top+bh+gap&&my<top+2*(bh+gap)){menuScale=computeUiScale();settingsOpen=true;return;}
        if(my>=top+2*(bh+gap)&&my<top+3*(bh+gap)){if(mx<x+bw/2)Nexus.musicEnabled=!Nexus.musicEnabled;else Nexus.sound=!Nexus.sound;return;}
        if(my>=top+3*(bh+gap)&&my<top+4*(bh+gap)){teleportOpen=true;teleportField=0;teleportValues[0]=formatCoordinate(px);teleportValues[1]=formatCoordinate(-py);teleportValues[2]=formatCoordinate(pz);teleportValues[3]=String.format(java.util.Locale.ROOT,"%.3f",Nexus.amp);return;}if(my>=top+4*(bh+gap)&&my<top+5*(bh+gap)){quitConfirm=true;}
    }
    private void playFootsteps(long now){if(flyMode||!grounded)return;double moved=Math.hypot(px-lastStepX,pz-lastStepZ);lastStepX=px;lastStepZ=pz;if(moved>.035&&now-lastStepSound>360_000_000L){byte below=Nexus.getBlock((long)Math.floor(px),(long)Math.floor(py+1.7),(long)Math.floor(pz));if(below!=Nexus.AIR)Nexus.block(below,2,px,py+1.5,pz);lastStepSound=now;}}

    private int createParticleProgram(){String vs="#version 150 core\nin vec3 aPosition; in vec4 aColor; out vec4 vColor; uniform mat4 uProjection; uniform mat4 uView; void main(){vColor=aColor;gl_Position=uProjection*uView*vec4(aPosition,1.0);gl_PointSize=12.0;}";String fs="#version 150 core\nin vec4 vColor; out vec4 fragColor; void main(){fragColor=vColor;}";int v=shader(GL_VERTEX_SHADER,vs),f=shader(GL_FRAGMENT_SHADER,fs),p=glCreateProgram();glAttachShader(p,v);glAttachShader(p,f);glBindAttribLocation(p,0,"aPosition");glBindAttribLocation(p,1,"aColor");glLinkProgram(p);if(glGetProgrami(p,GL_LINK_STATUS)==GL_FALSE)throw new IllegalStateException(glGetProgramInfoLog(p));glDeleteShader(v);glDeleteShader(f);return p;}
    private void initParticleBuffers(){particleVao=glGenVertexArrays();particleVbo=glGenBuffers();glBindVertexArray(particleVao);glBindBuffer(GL_ARRAY_BUFFER,particleVbo);glBufferData(GL_ARRAY_BUFFER,4L*7*Particles.CAP,GL_STREAM_DRAW);glVertexAttribPointer(0,3,GL_FLOAT,false,7*4,0L);glEnableVertexAttribArray(0);glVertexAttribPointer(1,4,GL_FLOAT,false,7*4,3L*4);glEnableVertexAttribArray(1);glBindVertexArray(0);}
    private void drawParticles(){int n=Particles.count;if(n==0)return;double ox=Math.floor(px/CHUNK)*CHUNK,oy=Math.floor(py/CHUNK)*CHUNK,oz=Math.floor(pz/CHUNK)*CHUNK;float[] projection=perspective((float)Math.toRadians(fovDegrees),width/(float)height,.05f,Math.max(1000f,renderDistance*CHUNK*2f));float fx=(float)(Math.sin(yaw)*Math.cos(pitch)),fy=(float)Math.sin(pitch),fz=(float)(-Math.cos(yaw)*Math.cos(pitch));float[] view=lookAt((float)(px-ox),(float)-(py-oy),(float)(pz-oz),(float)(px-ox)+fx,(float)-(py-oy)+fy,(float)(pz-oz)+fz,0,1,0);FloatBuffer b=particleData;b.clear();for(int i=0;i<n;i++){b.put((float)(Particles.pX[i]-ox)).put((float)-(Particles.pY[i]-oy)).put((float)(Particles.pZ[i]-oz));int c=Particles.color[i];float a=Math.min(1f,Particles.life[i]/20f);b.put(((c>>16)&255)/255f).put(((c>>8)&255)/255f).put((c&255)/255f).put(a);}b.flip();glUseProgram(particleProgram);glUniformMatrix4fv(glGetUniformLocation(particleProgram,"uProjection"),false,projection);glUniformMatrix4fv(glGetUniformLocation(particleProgram,"uView"),false,view);glBindBuffer(GL_ARRAY_BUFFER,particleVbo);glBufferData(GL_ARRAY_BUFFER,b,GL_STREAM_DRAW);glBindVertexArray(particleVao);glDrawArrays(GL_POINTS,0,n);glBindVertexArray(0);}

    private int reloadAtlasTexture(){if(atlasTexture!=0)glDeleteTextures(atlasTexture);return uploadAtlas();}
    private int uploadAtlas(){int tex=glGenTextures();glBindTexture(GL_TEXTURE_2D,tex);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MIN_FILTER,GL_NEAREST);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MAG_FILTER,GL_NEAREST);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_WRAP_S,GL_REPEAT);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_WRAP_T,GL_REPEAT);
        ByteBuffer rgba=memAlloc(Nexus.atlas.length*4);for(int i=0;i<Nexus.atlas.length;i++){int c=Nexus.atlas[i];rgba.put((byte)(c>>16)).put((byte)(c>>8)).put((byte)c).put((byte)(c>>>24));}rgba.flip();glPixelStorei(GL_UNPACK_ALIGNMENT,1);glTexImage2D(GL_TEXTURE_2D,0,GL_RGBA8,Nexus.texRes,ATLAS_H,0,GL_RGBA,GL_UNSIGNED_BYTE,rgba);memFree(rgba);return tex;
    }
    private int createProgram(){String vs="#version 150 core\nin vec3 aPosition; in vec2 aUV; in float aTile; in float aShade; out vec2 vUV; out float vTile; out float vShade; out float vAO; out vec3 vWorldPos; uniform mat4 uProjection; uniform mat4 uView; uniform vec3 uChunkOrigin; void main(){vUV=aUV;vTile=aTile;vShade=aShade;vAO=1.0;vWorldPos=aPosition+uChunkOrigin;gl_Position=uProjection*uView*vec4(vWorldPos,1.0);}";
        String fs="#version 150 core\nin vec2 vUV; in float vTile; in float vShade; in float vAO; in vec3 vWorldPos; out vec4 fragColor; uniform sampler2D uAtlas; uniform vec3 uSunColor; uniform vec3 uAmbientColor; uniform vec3 uCameraPos; uniform vec3 uFogColor; uniform float uFogDensity; uniform float uFogDistance; uniform int uClassic; void main(){vec2 uv=vec2(fract(vUV.x),(vTile+fract(vUV.y))/108.0);vec4 c=texture(uAtlas,uv);float id=floor(vTile/3.0);if(id==13.0)c.a=1.0;if(c.a<0.08)discard;float emission=(id==11.0?0.90:(id==16.0||id==18.0?0.30:(id==17.0?0.25:(id==14.0?0.25:(id==15.0?0.20:0.0)))));vec3 rgb;if(uClassic==1){rgb=c.rgb*(vShade+emission);}else{float distToCamera=length(vWorldPos-uCameraPos);float lantern=(1.0-clamp(max(uAmbientColor.r,max(uAmbientColor.g,uAmbientColor.b)),0.0,1.0))*max(0.0,1.0-distToCamera/18.0)*0.70;vec3 ambient=max(uAmbientColor,vec3(0.18,0.18,0.20));vec3 light=ambient*(0.72+0.28*vAO)+uSunColor*vShade*vAO;rgb=c.rgb*light+c.rgb*emission+c.rgb*vec3(1.0,0.78,0.48)*lantern;}float alpha=c.a*(id==6.0?0.72:1.0);float d=length(vWorldPos-uCameraPos);float fog=clamp(d*uFogDensity/max(1.0,uFogDistance),0.0,1.0);rgb=mix(rgb,uFogColor,fog);fragColor=vec4(rgb,alpha);} ";
        int v=shader(GL_VERTEX_SHADER,vs),f=shader(GL_FRAGMENT_SHADER,fs),p=glCreateProgram();glAttachShader(p,v);glAttachShader(p,f);glBindAttribLocation(p,0,"aPosition");glBindAttribLocation(p,1,"aUV");glBindAttribLocation(p,2,"aTile");glBindAttribLocation(p,3,"aShade");glBindAttribLocation(p,4,"aAO");glLinkProgram(p);if(glGetProgrami(p,GL_LINK_STATUS)==GL_FALSE)throw new IllegalStateException(glGetProgramInfoLog(p));glDeleteShader(v);glDeleteShader(f);return p;}
    private int shader(int type,String src){int s=glCreateShader(type);glShaderSource(s,src);glCompileShader(s);if(glGetShaderi(s,GL_COMPILE_STATUS)==GL_FALSE)throw new IllegalStateException(glGetShaderInfoLog(s));return s;}
    private static float[] perspective(float fov,float aspect,float near,float far){float f=1f/(float)Math.tan(fov/2f);float[] m=new float[16];m[0]=f/aspect;m[5]=f;m[10]=(far+near)/(near-far);m[11]=-1;m[14]=(2*far*near)/(near-far);return m;}
    private static float[] lookAt(float ex,float ey,float ez,float cx,float cy,float cz,float ux,float uy,float uz){float fx=cx-ex,fy=cy-ey,fz=cz-ez,fl=(float)Math.sqrt(fx*fx+fy*fy+fz*fz);fx/=fl;fy/=fl;fz/=fl;float sx=fy*uz-fz*uy,sy=fz*ux-fx*uz,sz=fx*uy-fy*ux,sl=(float)Math.sqrt(sx*sx+sy*sy+sz*sz);sx/=sl;sy/=sl;sz/=sl;float vx=sy*fz-sz*fy,vy=sz*fx-sx*fz,vz=sx*fy-sy*fx;return new float[]{sx,vx,-fx,0,sy,vy,-fy,0,sz,vz,-fz,0,-(sx*ex+sy*ey+sz*ez),-(vx*ex+vy*ey+vz*ez),fx*ex+fy*ey+fz*ez,1};}

    private static final class GeneratedChunk{final long x,y,z;final byte[] data;final int epoch;GeneratedChunk(long x,long y,long z,byte[]d,int e){this.x=x;this.y=y;this.z=z;data=d;epoch=e;}}
    private static final class MeshResult{final long x,y,z;final MeshPair mesh;final int epoch;MeshResult(long x,long y,long z,MeshPair m,int e){this.x=x;this.y=y;this.z=z;mesh=m;epoch=e;}}
    private static final class GpuMesh{final int vao,vbo,ebo,count;GpuMesh(int a,int b,int e,int n){vao=a;vbo=b;ebo=e;count=n;}void destroy(){if(vao!=0)glDeleteVertexArrays(vao);if(vbo!=0)glDeleteBuffers(vbo);if(ebo!=0)glDeleteBuffers(ebo);}}
    private static final class GpuChunk{final long x,y,z;double sortDistance;final int opaqueVao,opaqueVbo,opaqueEbo,opaqueCount,transparentVao,transparentVbo,transparentEbo,transparentCount;GpuChunk(long x,long y,long z,int oa,int ob,int oe,int oc,int ta,int tb,int te,int tc){this.x=x;this.y=y;this.z=z;opaqueVao=oa;opaqueVbo=ob;opaqueEbo=oe;opaqueCount=oc;transparentVao=ta;transparentVbo=tb;transparentEbo=te;transparentCount=tc;}void destroy(){new GpuMesh(opaqueVao,opaqueVbo,opaqueEbo,opaqueCount).destroy();new GpuMesh(transparentVao,transparentVbo,transparentEbo,transparentCount).destroy();}}
    private static final class Mesh{final FloatBuffer vertices;final IntBuffer indices;Mesh(FloatBuffer v,IntBuffer i){vertices=v;indices=i;}void free(){memFree(vertices);memFree(indices);}}
    private static final class MeshPair{final Mesh opaque,transparent;MeshPair(Mesh o,Mesh t){opaque=o;transparent=t;}void free(){opaque.free();transparent.free();}}

    private static final class GreedyMesher{
        // Primitive builders avoid millions of temporary Float/Integer objects during chunk meshing.
        private static final class Floats {
            float[] a = new float[4096]; int n;
            void add(float v){if(n==a.length)a=Arrays.copyOf(a,a.length*2);a[n++]=v;}
            FloatBuffer buffer(){FloatBuffer b=memAllocFloat(n);b.put(a,0,n).flip();return b;}
        }
        private static final class Ints {
            int[] a = new int[2048]; int n;
            void add(int v){if(n==a.length)a=Arrays.copyOf(a,a.length*2);a[n++]=v;}
            IntBuffer buffer(){IntBuffer b=memAllocInt(n);b.put(a,0,n).flip();return b;}
        }
        // Per-thread scratch: vertex/index builders and the 2D mask are reused between meshes instead of reallocated.
        private static final class Scratch{final Floats ov=new Floats(),tv=new Floats();final Ints oi=new Ints(),ti=new Ints();final int[] mask=new int[64*64],du=new int[3],dv=new int[3];}
        private static final ThreadLocal<Scratch> SCRATCH=ThreadLocal.withInitial(Scratch::new);
        private static final int SCRATCH_KEEP=1<<20; // don't let one huge mesh pin megabytes per thread forever

        // Which face (if any) belongs on the plane between voxel a and its +axis neighbour b.
        // Positive = a's +axis face, negative = b's -axis face. Rules:
        //  * air|solid -> the solid's face; opaque|opaque -> nothing
        //  * transparent|opaque -> ONLY the opaque block's face (the old code drew the transparent block's
        //    face into the opaque block and left the opaque block with no face -> see-through holes)
        //  * a face is emitted only by the chunk that OWNS the block (no duplicate boundary quads, which also
        //    double-blended glass/leaves on chunk borders)
        private static int faceFor(int a,int b,int plane,int size){
            if(a==0&&b==0)return 0;
            int face;
            if(b==0)face=a;
            else if(a==0)face=-b;
            else{
                boolean at=transparent(a),bt=transparent(b);
                if(!at&&!bt)return 0;
                if(at&&bt)face=(a==b)?0:a;
                else face=at?-b:a;
            }
            if(plane==-1&&face>0)return 0;
            if(plane==size-1&&face<0)return 0;
            return face;
        }

        static MeshPair build(byte[] vox,long worldX,long worldY,long worldZ){
            Scratch s=SCRATCH.get();
            Floats ov=s.ov,tv=s.tv;Ints oi=s.oi,ti=s.ti;ov.n=tv.n=0;oi.n=ti.n=0;
            int[] mask=s.mask;
            int[] dims={64,64,64}; int[] p={0,0,0};
            for(int d=0;d<3;d++){
                int u=(d+1)%3,w=(d+2)%3;int[] x={0,0,0};
                for(x[d]=-1;x[d]<dims[d];){
                    int n=0;
                    for(x[w]=0;x[w]<dims[w];x[w]++)for(x[u]=0;x[u]<dims[u];x[u]++){
                        int a=sample(vox,x[0],x[1],x[2]);
                        int b=sample(vox,x[0]+(d==0?1:0),x[1]+(d==1?1:0),x[2]+(d==2?1:0));
                        mask[n++]=faceFor(a,b,x[d],dims[d]);
                    }
                    x[d]++;n=0;
                    for(int j=0;j<dims[w];j++)for(int i=0;i<dims[u];){
                        int c=mask[n+j*dims[u]+i];if(c==0){i++;continue;}
                        int rw=1;while(i+rw<dims[u]&&mask[n+j*dims[u]+i+rw]==c)rw++;
                        int rh=1;boolean stop=false;
                        while(j+rh<dims[w]&&!stop){for(int k=0;k<rw;k++)if(mask[n+(j+rh)*dims[u]+i+k]!=c){stop=true;break;}if(!stop)rh++;}
                        int block=Math.abs(c);boolean positive=c>0;float shade=positive?1f:.76f;if(d==1)shade=positive?.55f:1f;int face=d==1?(positive?2:0):1;int tile=block*3+face;
                        p[0]=p[1]=p[2]=0;p[d]=x[d];int[] du=s.du,dv=s.dv;du[0]=du[1]=du[2]=dv[0]=dv[1]=dv[2]=0;p[u]=i;p[w]=j;du[u]=rw;dv[w]=rh;
                        quad(transparent(block)?tv:ov,transparent(block)?ti:oi,p,du,dv,tile,shade,positive,d);
                        for(int yy=0;yy<rh;yy++)for(int xx=0;xx<rw;xx++)mask[n+(j+yy)*dims[u]+i+xx]=0;
                        i+=rw;
                    }
                }
            }
            MeshPair out=new MeshPair(new Mesh(ov.buffer(),oi.buffer()),new Mesh(tv.buffer(),ti.buffer()));
            if(ov.a.length>SCRATCH_KEEP)ov.a=new float[4096];if(tv.a.length>SCRATCH_KEEP)tv.a=new float[4096];
            if(oi.a.length>SCRATCH_KEEP)oi.a=new int[2048];if(ti.a.length>SCRATCH_KEEP)ti.a=new int[2048];
            return out;
        }
        private static boolean transparent(int id){return id==Nexus.LEAVES||id==Nexus.GLASS;}
        private static int sample(byte[] a,int x,int y,int z){if(x< -1||x>64||y< -1||y>64||z< -1||z>64)return 0;return a[(x+1)+66*(z+1)+4356*(y+1)]&255;}
        private static float ambientOcclusion(byte[] vox,int[] c,int[] p,int[] du,int[] dv,int axis,boolean positive){return 1.0f;}
        private static void quad(Floats out,Ints idx,int[] p,int[] du,int[] dv,int tile,float shade,boolean positive,int axis){
            int base=out.n/7;
            float a=du[0]+du[1]+du[2],b=dv[0]+dv[1]+dv[2];
            int x0=p[0],y0=p[1],z0=p[2];
            int x1=x0+du[0],y1=y0+du[1],z1=z0+du[2];
            int x2=x1+dv[0],y2=y1+dv[1],z2=z1+dv[2];
            int x3=x0+dv[0],y3=y0+dv[1],z3=z0+dv[2];
            if(axis==2){vert(out,x0,y0,z0,0,0,tile,shade);vert(out,x1,y1,z1,a,0,tile,shade);vert(out,x2,y2,z2,a,b,tile,shade);vert(out,x3,y3,z3,0,b,tile,shade);}
            else{vert(out,x0,y0,z0,0,0,tile,shade);vert(out,x1,y1,z1,0,a,tile,shade);vert(out,x2,y2,z2,b,a,tile,shade);vert(out,x3,y3,z3,b,0,tile,shade);}
            if(positive){idx.add(base);idx.add(base+1);idx.add(base+2);idx.add(base);idx.add(base+2);idx.add(base+3);}
            else{idx.add(base);idx.add(base+2);idx.add(base+1);idx.add(base);idx.add(base+3);idx.add(base+2);}
        }
        private static void vert(Floats out,int x,int y,int z,float u,float v,int tile,float shade){out.add(x);out.add(-y);out.add(z);out.add(u);out.add(v);out.add(tile);out.add(shade);}
    }
}
