(()=>{
'use strict';
const $=id=>document.getElementById(id),canvas=$('glass'),ctx=canvas.getContext('2d',{alpha:true});
const W=500,H=670,CX=250,NECK=333,TOP=88,FLOOR=578,STEP=1/90,G=1400,FLIP_TIME=.82,FLOW_DELAY=.15,LEAD=1.3;
const reduced=matchMedia('(prefers-reduced-motion: reduce)').matches;
const clamp=(n,a,b)=>Math.min(b,Math.max(a,n));
const segments=s=>typeof Intl.Segmenter==='function'?[...new Intl.Segmenter('ja',{granularity:'grapheme'}).segment(s)].map(x=>x.segment):Array.from(s);
const curves=[[[110,80],[146,80],[145,142],[132,183]],[[132,183],[115,238],[15,292],[15,330]],[[15,330],[15,332],[15,334],[15,336]],[[15,336],[15,374],[115,428],[132,483]],[[132,483],[145,524],[146,586],[110,586]]];
const widths=new Float32Array(H+1),slopes=new Float32Array(H+1),samples=[];
for(const s of curves)for(let i=0;i<=256;i++){const t=i/256,u=1-t;samples.push([s[0][0]*u*u*u+3*s[1][0]*u*u*t+3*s[2][0]*u*t*t+s[3][0]*t*t*t,s[0][1]*u*u*u+3*s[1][1]*u*u*t+3*s[2][1]*u*t*t+s[3][1]*t*t*t]);}
let si=0;for(let y=0;y<=H;y++){while(si<samples.length-2&&samples[si+1][1]<y)si++;const a=samples[si],b=samples[si+1];widths[y]=y<80||y>586?110:a[0]+(b[0]-a[0])*clamp((y-a[1])/Math.max(.001,b[1]-a[1]),0,1);}
for(let y=1;y<H;y++)slopes[y]=(widths[y+1]-widths[y-1])*.5;
const halfWidth=y=>widths[Math.round(clamp(y,0,H))];
function throatHalfWidth(y){
 const base=halfWidth(y),dy=Math.abs(y-NECK);
 if(dy>70)return base;
 const t=1-dy/70;
 const textActive=shapeA==='text'||(colorMode==='mix'&&shapeB==='text');
 const minHalf=textActive?Math.max(6.2,R*1.95):Math.max(3.2,R*1.65);
 const target=Math.min(base,minHalf+dy*.115);
 return base*(1-t)+target*t;
}
const glassPath=new Path2D();glassPath.moveTo(CX-110,80);glassPath.lineTo(CX+110,80);
for(const s of curves)glassPath.bezierCurveTo(CX+s[1][0],s[1][1],CX+s[2][0],s[2][1],CX+s[3][0],s[3][1]);
glassPath.lineTo(CX-110,586);for(const s of [...curves].reverse())glassPath.bezierCurveTo(CX-s[2][0],s[2][1],CX-s[1][0],s[1][1],CX-s[0][0],s[0][1]);glassPath.closePath();
let state='idle',duration=30,elapsed=0,carry=0,anchor=0,simTime=0,accumulator=0,lastFrame=performance.now(),lastHUD=-1;
let shapeA='circle',lettersA='推し',glyphsA=['推','し'],shapeB='star',lettersB='★',glyphsB=['★'];
let sizeSetting=45,D=4.575,R=2.1,color='#edb969',rgb=[237,185,105],colorB='#8bb9ed',rgbB=[139,185,237];
let colorMode='single',mixRatio=50,mixLayout='mixed';
let particles=[],capacity=0,N=0,sprites=[],passed=0,granted=0,landings=0;
let flipProgress=0,flipStarted=0,frameTurn=0,doneAt=-100,settleUntil=0,ripples=[],needsRebuild=false;
let seed=719,CELL=6,COLS=85,ROWS=113,head=new Int32Array(COLS*ROWS),links=new Int32Array(1);
const rnd=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed/4294967296;};
const now=()=>performance.now()/1000;
const THEME_KEY='oshiglass.theme';
let theme=document.documentElement.dataset.theme==='light'?'light':'dark';
function syncThemeUI(){
 document.documentElement.dataset.theme=theme;
 document.querySelectorAll('.theme-option').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.themeChoice===theme)));
 const meta=$('themeColorMeta');if(meta)meta.setAttribute('content',theme==='light'?'#f4f1eb':'#0d1015');
}
function setTheme(next){
 if(next!=='dark'&&next!=='light'||next===theme)return;theme=next;
 try{localStorage.setItem(THEME_KEY,theme);}catch{}
 syncThemeUI();renderLayers();draw(performance.now()/1000);
}
const hexMix=(base,v,t)=>`rgb(${base.map(c=>Math.round(c*(1-t)+v*t)).join(',')})`;
function formatTime(t){const s=Math.max(0,Math.ceil(t-1e-6));return `${String(Math.floor(s/60)).padStart(2,'0')}:${String(s%60).padStart(2,'0')}`;}
// Every visible grain is one persistent physical body. No bulk image, replacement
// grain, fade-out, or appearance driven by elapsed time. Only a metered gate uses time.
function assignMixLayout(){
 if(!particles.length)return;
 for(const p of particles)p.mix=0;
 if(colorMode!=='mix')return;
 const countA=clamp(Math.round(N*mixRatio/100),0,N);
 if(countA<=0){for(const p of particles)p.mix=1;return;}
 if(countA>=N)return;
 const ordered=[...particles];
 if(mixLayout==='mixed'){
   let local=0x6d2b79f5;
   const rr=()=>{local=(Math.imul(local,1664525)+1013904223)>>>0;return local/4294967296;};
   for(let i=ordered.length-1;i>0;i--){const j=Math.floor(rr()*(i+1));[ordered[i],ordered[j]]=[ordered[j],ordered[i]];}
   for(let i=countA;i<ordered.length;i++)ordered[i].mix=1;
 }else if(mixLayout==='leftRight'){
   ordered.sort((a,b)=>a.x-b.x||a.y-b.y);
   for(let i=countA;i<ordered.length;i++)ordered[i].mix=1;
 }else if(mixLayout==='topBottom'){
   ordered.sort((a,b)=>a.y-b.y||a.x-b.x);
   for(let i=countA;i<ordered.length;i++)ordered[i].mix=1;
 }else{
   ordered.sort((a,b)=>a.y-b.y||a.x-b.x);
   const topA=Math.floor(countA/2),bottomA=countA-topA;
   for(let i=topA;i<ordered.length-bottomA;i++)ordered[i].mix=1;
 }
}
function rebuildField(){
 glyphsA=segments(lettersA).filter(x=>x.trim());if(!glyphsA.length)glyphsA=['推'];
 glyphsB=segments(lettersB).filter(x=>x.trim());if(!glyphsB.length)glyphsB=['★'];
 const textActive=shapeA==='text'||(colorMode==='mix'&&shapeB==='text');
 D=textActive?4.3+sizeSetting*.064:3.0+sizeSetting*.047;
 R=D*(textActive?.54:.50);CELL=Math.ceil(2.15*R);COLS=Math.ceil(W/CELL)+2;ROWS=Math.ceil(H/CELL)+2;head=new Int32Array(COLS*ROWS);
 const slots=[];seed=719;let row=0;const dx=2.07*R,dy=1.81*R;
 for(let y=FLOOR-R-.5;y>NECK+R+18;y-=dy,row++){
   const w=halfWidth(y)-R*Math.sqrt(1+slopes[Math.round(y)]**2)-.7;
   for(let x=CX+(-Math.floor(w/dx)+(row%2)*.5)*dx;x<CX+w;x+=dx){
     if(x<CX-w)continue;
     slots.push({x,y,key:FLOOR-y+.43*Math.abs(x-CX)+(rnd()-.5)*R*.1});
   }
 }
 slots.sort((a,b)=>a.key-b.key);capacity=slots.length;
 const fill=clamp(.57+.052*Math.log2(Math.max(1,duration/10)),.57,.82);
 N=Math.min(2400,Math.floor(capacity*fill));links=new Int32Array(N);
 particles=slots.slice(0,N).map((s,id)=>({id,x:s.x,y:s.y,px:s.x,py:s.y,r:R*(.97+rnd()*.03),glyph:id,shade:Math.floor(rnd()*6),angle:(rnd()-.5)*.5,readAngle:(rnd()-.5)*.45,spin:(rnd()-.5)*1.1,lower:true,allowed:true,landed:true,sleep:false,rest:0,supportL:false,supportR:false,roll:0,rollDir:id%2?1:-1,mix:0}));
 for(let i=0;i<45;i++)physics(STEP);
 for(const p of particles){p.px=p.x;p.py=p.y;p.sleep=true;}
 passed=0;landings=0;granted=0;simTime=0;accumulator=0;assignMixLayout();makeSprites();
 $('sizeValue').textContent=`${sizeSetting} / 100 · ${N.toLocaleString()}粒`;
 $('grainSize').setAttribute('aria-valuetext',`${sizeSetting} / 100、${N}粒`);
}
function confine(p){
 if(p.y<TOP+p.r){p.y=TOP+p.r;p.py=Math.min(p.py,p.y);}
 if(p.y>FLOOR-p.r){const dy=p.y-p.py;p.y=FLOOR-p.r;p.py=p.y+Math.max(0,dy)*.025;p.px=p.x-(p.x-p.px)*.92;p.supportL=p.supportR=true;if(!p.landed)land(p);}
 // One-way metering gate. The body waits here and then moves through the same
 // opening under gravity. Nothing moves it to an outlet position.
 const gate=NECK-9-p.r;
 if(!p.lower&&!p.allowed&&p.y>gate){p.y=gate;p.py=Math.min(p.py,p.y);}
 for(let k=0;k<2;k++){
   const iy=Math.round(clamp(p.y,81,585)),s=slopes[iy],baseLimit=halfWidth(p.y),neckLimit=throatHalfWidth(p.y),limit=Math.max(.5,Math.min(baseLimit,neckLimit)-p.r*Math.sqrt(1+s*s)),dx=p.x-CX,pen=Math.abs(dx)-limit;
   if(pen>0){const sign=dx<0?-1:1,den=1+s*s;p.x-=sign*pen/den;p.y+=s*pen/den;
     const vx=p.x-p.px,vy=p.y-p.py,dot=(vx*sign-vy*s)/den;
     if(dot>0){p.px+=sign*dot*1.025;p.py-=s*dot*1.025;}
   }
 }
 p.y=clamp(p.y,TOP+p.r,FLOOR-p.r);
 if(!p.lower&&!p.allowed&&p.y>gate){p.y=gate;p.py=Math.min(p.py,p.y);}
}
function land(p){p.landed=true;landings++;p.roll=.32;p.rest=0;p.rollDir=Math.abs(p.x-CX)>3?Math.sign(p.x-CX):(p.id%2?1:-1);p.px-=p.rollDir*.11;}
function meter(){
 const target=Math.min(N,Math.floor(clamp((elapsed-FLOW_DELAY)/(duration-FLOW_DELAY-LEAD),0,1)*N));
 // Grant only a few grains near the lip at once so the waist keeps a narrow,
 // believable stream, especially when the grains are very small.
 let pending=particles.reduce((n,p)=>n+(!p.lower&&p.allowed?1:0),0);
 const lanes=Math.max(1,Math.round((throatHalfWidth(NECK)*2)/Math.max(2.6,2*R)));
 const maxPending=clamp(lanes*2+1,3,9);
 while(granted<target&&pending<maxPending){
   let best=null,score=Infinity;
   for(const p of particles)if(!p.lower&&!p.allowed){const d=NECK-p.y+Math.abs(p.x-CX)*(.38+.8/Math.max(1.2,R));if(d<score){score=d;best=p;}}
   if(!best)break;best.allowed=true;best.sleep=false;best.rest=0;granted++;pending++;
 }
}
function physics(dt){
 for(const p of particles){
   if(p.sleep)continue;p.sx=p.x;p.sy=p.y;
   const supported=p.supportL||p.supportR;p.supportL=p.supportR=false;
   let vx=clamp((p.x-p.px)*.996,-9,9),vy=clamp((p.y-p.py)*.998,-10,10);p.px=p.x;p.py=p.y;
   p.x+=vx;p.y+=vy+G*dt*dt;
   if(!p.lower){
     // Slippery funnel and a stronger neck-centering pull keep the waist from
     // looking too wide when the grains are tiny.
     const neckFactor=clamp(1-Math.abs(p.y-NECK)/92,0,1);
     p.x+=clamp(CX-p.x,-25,25)*(2.15+4.2*neckFactor)*dt*dt;
     if(p.allowed&&p.y>NECK-62)p.y+=(1360+560*neckFactor)*dt*dt;
   }else if(p.roll>0){p.roll-=dt;if(supported)p.x+=p.rollDir*20*dt*dt;}
   const pShape=(colorMode==='mix'&&p.mix===1)?shapeB:shapeA;
   if(pShape==='text'){const da=Math.atan2(Math.sin(p.readAngle-p.angle),Math.cos(p.readAngle-p.angle));p.angle+=da*.025+clamp(vx*.006,-.025,.025);}
   else p.angle+=clamp(vx*.025+p.spin*Math.abs(vy)*.002,-.07,.07);
   confine(p);
 }
 for(let it=0;it<(N>1400?3:4);it++){
   head.fill(-1);
   for(let i=0;i<N;i++){const p=particles[i],c=clamp(Math.floor(p.x/CELL),0,COLS-1),r=clamp(Math.floor(p.y/CELL),0,ROWS-1),key=r*COLS+c;links[i]=head[key];head[key]=i;}
   for(let i=0;i<N;i++){
     const p=particles[i];if(p.sleep)continue;const c=clamp(Math.floor(p.x/CELL),1,COLS-2),r=clamp(Math.floor(p.y/CELL),1,ROWS-2);
     for(let yy=r-1;yy<=r+1;yy++)for(let xx=c-1;xx<=c+1;xx++)for(let j=head[yy*COLS+xx];j!==-1;j=links[j]){
       const q=particles[j];if(j===i||(!q.sleep&&j<i))continue;
       let dx=q.x-p.x,dy=q.y-p.y,dd=dx*dx+dy*dy,rr=p.r+q.r;
       if(dd>=rr*rr)continue;if(dd<1e-6){dx=.001;dy=.001;dd=.000002;}
       const dist=Math.sqrt(dd),nx=dx/dist,ny=dy/dist;
       if(p.lower&&q.lower){
         if(ny>.28){if(dx<0)p.supportL=true;else p.supportR=true;if(it===0&&!p.landed)land(p);}
         if(ny<-.28){if(dx>0)q.supportL=true;else q.supportR=true;if(it===0&&!q.landed)land(q);}
         if(ny>.93)p.supportL=p.supportR=true;if(ny<-.93)q.supportL=q.supportR=true;
       }
       const ip=p.sleep?0:1,iq=q.sleep?0:1,mass=ip+iq,overlap=(rr-dist)*.93/mass;
       p.x-=nx*overlap*ip;p.y-=ny*overlap*ip;q.x+=nx*overlap*iq;q.y+=ny*overlap*iq;
       if(it===0){
         const rvx=(q.x-q.px)-(p.x-p.px),rvy=(q.y-q.py)-(p.y-p.py),vn=rvx*nx+rvy*ny;
         if(vn<0){const impulse=vn*1.025/mass;p.px-=nx*impulse*ip;p.py-=ny*impulse*ip;q.px+=nx*impulse*iq;q.py+=ny*impulse*iq;}
         const friction=p.lower&&q.lower?(p.roll>0||q.roll>0?.045:.24):.005;
         const tangent=clamp(rvx*(-ny)+rvy*nx,-.5,.5)*friction/mass;
         p.px+=ny*tangent*ip;p.py-=nx*tangent*ip;q.px-=ny*tangent*iq;q.py+=nx*tangent*iq;
       }
     }
   }
   for(const p of particles)if(!p.sleep)confine(p);
 }
 for(const p of particles){
   // Limit solver corrections under pressure at the metering lip. A contact
   // cannot throw a tiny waiting grain across the whole neck in one time step.
   if(!p.sleep){const dx=p.x-p.sx,dy=p.y-p.sy,d=Math.hypot(dx,dy),limit=!p.lower&&!p.allowed?Math.max(3,p.r*2):14;if(d>limit){p.x=p.sx+dx*limit/d;p.y=p.sy+dy*limit/d;}}
   if(!p.lower&&p.y>NECK+2){p.lower=true;passed++;}
   if(!p.lower||p.sleep)continue;
   if(p.supportL&&p.supportR&&p.roll<=0&&Math.hypot(p.x-p.px,p.y-p.py)<.12)p.rest++;else p.rest=0;
   if(p.rest>28){p.sleep=true;p.px=p.x;p.py=p.y;}
 }
}
function step(dt){simTime+=dt;meter();physics(dt);}

function makeSprites(){
 sprites=[];
 const configs=colorMode==='mix'?
   [{base:rgb,shape:shapeA,glyphs:glyphsA},{base:rgbB,shape:shapeB,glyphs:glyphsB}]:
   [{base:rgb,shape:shapeA,glyphs:glyphsA}];
 for(const cfg of configs){
   const variants=[];
   const count=cfg.shape==='text'?cfg.glyphs.length:1;
   for(let k=0;k<count;k++){
     const shades=[];
     for(let i=0;i<6;i++){
       const c=document.createElement('canvas');c.width=c.height=96;const g=c.getContext('2d');g.scale(3,3);g.translate(16,16);
       const fill=hexMix(cfg.base,i%2?0:255,i%2?.05+i*.025:.08+i*.025);
       if(cfg.shape==='circle'){
         g.fillStyle=fill;g.beginPath();g.ellipse(0,0,D*.46,D*.42,(i-3)*.2,0,Math.PI*2);g.fill();g.fillStyle=hexMix(cfg.base,255,.42);g.beginPath();g.arc(-D*.13,-D*.13,Math.max(.28,D*.095),0,Math.PI*2);g.fill();
       }else if(cfg.shape==='star'){
         g.fillStyle=fill;g.beginPath();for(let j=0;j<10;j++){const a=j*Math.PI/5-Math.PI/2,r=j%2?D*.24:D*.50;g.lineTo(Math.cos(a)*r,Math.sin(a)*r);}g.closePath();g.fill();
       }else{
         g.font=`600 ${D}px "Yu Gothic",Meiryo,"Noto Sans JP",sans-serif`;g.textAlign='center';g.textBaseline='middle';g.fillStyle=hexMix(cfg.base,255,.12+i*.023);g.fillText(cfg.glyphs[k],0,.15);
       }
       shades.push(c);
     }
     variants.push(shades);
   }
   sprites.push({shape:cfg.shape,glyphs:cfg.glyphs,variants});
 }
}
// Offscreen frame layers keep the glass and metal cheap to redraw.
const back=document.createElement('canvas'),front=document.createElement('canvas');let dpr=1;
function rounded(g,x,y,w,h,r){g.beginPath();g.roundRect(x,y,w,h,r);}
function renderLayers(){
 for(const c of [back,front]){c.width=Math.round(W*dpr);c.height=Math.round(H*dpr);}
 const b=back.getContext('2d'),f=front.getContext('2d'),light=theme==='light';b.scale(dpr,dpr);f.scale(dpr,dpr);
 // Ground and muted light pool.
 let grad=b.createRadialGradient(CX,610,12,CX,610,170);grad.addColorStop(0,light?'rgba(76,64,50,.20)':'rgba(0,0,0,.75)');grad.addColorStop(1,'rgba(0,0,0,0)');b.save();b.translate(0,465);b.scale(1,.23);b.fillStyle=grad;b.fillRect(30,390,440,440);b.restore();
 grad=b.createRadialGradient(CX,390,10,CX,390,225);grad.addColorStop(0,`rgba(${rgb},.035)`);grad.addColorStop(1,'rgba(0,0,0,0)');b.fillStyle=grad;b.fillRect(35,140,430,480);
 for(const x of [72,414]){
   let pole=b.createLinearGradient(x,0,x+14,0);
   if(light){pole.addColorStop(0,'#8c795f');pole.addColorStop(.3,'#b29a76');pole.addColorStop(.5,'#d0b68c');pole.addColorStop(.62,'#9a8364');pole.addColorStop(1,'#756650');}
   else{pole.addColorStop(0,'#13161b');pole.addColorStop(.3,'#3c3832');pole.addColorStop(.5,'#60554a');pole.addColorStop(.62,'#302c28');pole.addColorStop(1,'#13161c');}
   b.fillStyle=pole;rounded(b,x,66,14,532,5);b.fill();b.fillStyle=light?'rgba(255,248,226,.28)':'rgba(217,190,142,.12)';b.fillRect(x+3,92,1,475);
   for(const y of [93,563]){b.fillStyle=light?'#8d7a60':'#464038';rounded(b,x-2,y,18,7,2);b.fill();b.fillStyle=light?'#665946':'#1c1c1e';b.fillRect(x-2,y+5,18,2);}
 }
 // Smoke-tinted glass and inner edge, above the rear columns.
 grad=b.createLinearGradient(117,0,385,0);
 if(light){grad.addColorStop(0,'rgba(93,111,128,.11)');grad.addColorStop(.09,'rgba(255,255,255,.30)');grad.addColorStop(.36,'rgba(132,146,158,.055)');grad.addColorStop(.68,'rgba(255,255,255,.19)');grad.addColorStop(.93,'rgba(99,115,130,.10)');grad.addColorStop(1,'rgba(76,94,111,.15)');}
 else{grad.addColorStop(0,'rgba(183,194,204,.09)');grad.addColorStop(.09,'rgba(214,221,221,.025)');grad.addColorStop(.36,'rgba(21,25,31,.2)');grad.addColorStop(.68,'rgba(148,159,170,.025)');grad.addColorStop(.93,'rgba(211,217,216,.09)');grad.addColorStop(1,'rgba(231,238,235,.13)');}
 b.fillStyle=grad;b.fill(glassPath);b.strokeStyle=light?'rgba(78,96,113,.28)':'rgba(210,219,220,.17)';b.lineWidth=1.4;b.stroke(glassPath);
 // Front reflections follow the contour and fade toward the waist.
 f.save();f.clip(glassPath);
 grad=f.createLinearGradient(110,0,385,0);
 if(light){grad.addColorStop(0,'rgba(72,91,109,.16)');grad.addColorStop(.06,'rgba(255,255,255,.28)');grad.addColorStop(.32,'rgba(255,255,255,0)');grad.addColorStop(.86,'rgba(255,255,255,0)');grad.addColorStop(.97,'rgba(72,91,109,.10)');grad.addColorStop(1,'rgba(61,79,96,.18)');}
 else{grad.addColorStop(0,'rgba(242,244,237,.14)');grad.addColorStop(.06,'rgba(255,255,255,.025)');grad.addColorStop(.32,'rgba(255,255,255,0)');grad.addColorStop(.86,'rgba(255,255,255,0)');grad.addColorStop(.97,'rgba(219,232,242,.08)');grad.addColorStop(1,'rgba(236,239,244,.16)');}
 f.fillStyle=grad;f.fill(glassPath);
 // Highlights trace the actual glass contour, avoiding floating inner outlines.
 f.lineCap='round';
 for(const side of [-1,1]){
   const shine=f.createLinearGradient(0,90,0,580);
   if(light){shine.addColorStop(0,'rgba(61,83,102,.04)');shine.addColorStop(.18,'rgba(61,83,102,.20)');shine.addColorStop(.43,'rgba(61,83,102,0)');shine.addColorStop(.58,'rgba(61,83,102,0)');shine.addColorStop(.82,'rgba(61,83,102,.12)');shine.addColorStop(1,'rgba(61,83,102,0)');}
   else{shine.addColorStop(0,'rgba(234,242,250,.03)');shine.addColorStop(.18,'rgba(234,242,250,.23)');shine.addColorStop(.43,'rgba(234,242,250,0)');shine.addColorStop(.58,'rgba(234,242,250,0)');shine.addColorStop(.82,'rgba(234,242,250,.13)');shine.addColorStop(1,'rgba(234,242,250,0)');}
   f.strokeStyle=shine;f.lineWidth=side<0?2.2:1.2;f.beginPath();
   for(let y=91;y<578;y++){const x=CX+side*(halfWidth(y)-7);if(y===91)f.moveTo(x,y);else f.lineTo(x,y);}f.stroke();
 }
 f.restore();
 // Brushed brass caps; subtle chamfers instead of a flat rectangular frame.
 for(const [y,h]of[[59,27],[580,27]]){
   const cap=f.createLinearGradient(0,y,0,y+h);
   if(light){cap.addColorStop(0,'#b7a17d');cap.addColorStop(.055,'#d5bd92');cap.addColorStop(.15,'#9a8566');cap.addColorStop(.45,'#7b6a54');cap.addColorStop(.9,'#5c5042');cap.addColorStop(1,'#947e60');}
   else{cap.addColorStop(0,'#756957');cap.addColorStop(.055,'#9d8c71');cap.addColorStop(.15,'#4e4539');cap.addColorStop(.45,'#39342e');cap.addColorStop(.9,'#211f1e');cap.addColorStop(1,'#554936');}
   f.fillStyle=cap;rounded(f,60,y,380,h,7);f.fill();f.strokeStyle=light?'rgba(95,78,54,.25)':'rgba(216,194,153,.17)';f.lineWidth=.7;f.stroke();
   const sheen=f.createLinearGradient(70,0,430,0);sheen.addColorStop(0,'rgba(241,219,176,0)');sheen.addColorStop(.27,'rgba(241,219,176,.23)');sheen.addColorStop(.67,'rgba(241,219,176,.04)');sheen.addColorStop(1,'rgba(241,219,176,0)');f.fillStyle=sheen;f.fillRect(69,y+3,362,1);
   f.fillStyle=light?'#75654f':'#292622';rounded(f,82,y+(y<100?-6:h-1),336,8,3);f.fill();f.fillStyle=light?'rgba(255,241,207,.25)':'rgba(233,206,160,.16)';f.fillRect(91,y+(y<100?-5:h-1),318,1);
 }
 // Tiny polished feet and engraved maker's mark.
 f.fillStyle=light?'#6d604d':'#262521';for(const x of[84,390]){rounded(f,x,613,26,6,2);f.fill();rounded(f,x,47,26,6,2);f.fill();}
 f.textAlign='center';f.font='8px Arial';f.letterSpacing='3px';f.fillStyle=light?'rgba(255,239,204,.62)':'rgba(212,194,160,.55)';f.fillText('O S H I G L A S S',CX,599);
}

function resize(){const box=canvas.getBoundingClientRect();dpr=Math.min(2.25,Math.max(1,(window.devicePixelRatio||1)*box.width/W));canvas.width=Math.round(W*dpr);canvas.height=Math.round(H*dpr);renderLayers();draw(performance.now()/1000);}
function drawSeed(p,x,y){
 const spec=sprites[colorMode==='mix'?(p.mix||0):0],index=spec.shape==='text'?p.glyph%spec.glyphs.length:0,s=spec.variants[index][p.shade];
 if(spec.shape==='circle'){ctx.drawImage(s,x-16,y-16,32,32);}else{ctx.save();ctx.translate(x,y);ctx.rotate(p.angle);ctx.drawImage(s,-16,-16,32,32);ctx.restore();}
}
function draw(t){
 ctx.setTransform(dpr,0,0,dpr,0,0);ctx.clearRect(0,0,W,H);
 const turning=state==='flipping',ease=flipProgress*flipProgress*(3-2*flipProgress),a=turning?Math.PI*ease:0,scale=turning?1-.37*Math.sin(a):1;
 function turn(angle){ctx.translate(CX,NECK);ctx.rotate(angle);ctx.scale(scale,scale);ctx.translate(-CX,-NECK);}
 ctx.save();turn(frameTurn+a);ctx.drawImage(back,0,0,W,H);ctx.restore();
 ctx.save();turn(a);ctx.clip(glassPath);
 for(const p of particles)drawSeed(p,p.x,p.y);
 ctx.globalAlpha=1;
 const glow=Math.max(0,1-(t-doneAt)/2.5);if(glow>0&&!reduced){const g=ctx.createRadialGradient(CX,510,0,CX,510,155);g.addColorStop(0,`rgba(${rgb},${glow*.14})`);g.addColorStop(1,`rgba(${rgb},0)`);ctx.fillStyle=g;ctx.fillRect(105,365,290,225);}
 ctx.restore();ctx.save();turn(frameTurn+a);ctx.drawImage(front,0,0,W,H);ctx.restore();
 for(let i=ripples.length-1;i>=0;i--){const q=ripples[i],age=t-q.t;if(age>.65){ripples.splice(i,1);continue;}ctx.strokeStyle=`rgba(${rgb},${(1-age/.65)*.25})`;ctx.lineWidth=.8;ctx.beginPath();ctx.arc(q.x,q.y,9+age*44,0,Math.PI*2);ctx.stroke();}
}
const presetColors=new Set([...document.querySelectorAll('.swatch[data-channel="a"]')].map(b=>b.dataset.color.toLowerCase()));
const CUSTOM_UI_ACCENT='#a997e7',CUSTOM_UI_RGB=[169,151,231];
function updateChannelUI(channel,value){
 const picker=$(channel==='a'?'colorPickerA':'colorPickerB'),hex=$(channel==='a'?'hexColorA':'hexColorB');
 picker.value=value;hex.value=value.toUpperCase();
 document.querySelectorAll(`.swatch[data-channel="${channel}"]`).forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.color===value)));
 document.documentElement.style.setProperty(channel==='a'?'--sand-a':'--sand-b',value);
 if(channel==='b'){
   const card=document.querySelector('.sand-card-b');
   if(card){
     card.style.setProperty('--sand-b-local',value);
     const textInput=$('particleTextB');if(textInput)textInput.style.color=value;
     if(hex)hex.style.color=value;
     card.querySelectorAll('.shape').forEach(btn=>{
       const active=btn.getAttribute('aria-pressed')==='true';
       btn.style.color=active?value:'';
       btn.style.borderColor=active?value:'';
       btn.style.background=active?`color-mix(in srgb, ${value} 10%, transparent)`:'';
     });
   }
 }
}
function setColor(channel,value){
 value=value.toLowerCase();const nextRgb=[1,3,5].map(i=>parseInt(value.slice(i,i+2),16));
 if(channel==='b'){colorB=value;rgbB=nextRgb;updateChannelUI('b',colorB);makeSprites();draw(performance.now()/1000);return;}
 color=value;rgb=nextRgb;updateChannelUI('a',color);
 const preset=presetColors.has(color),uiHex=preset?color:CUSTOM_UI_ACCENT,uiRgb=preset?[...rgb]:CUSTOM_UI_RGB;
 document.documentElement.style.setProperty('--accent',uiHex);document.documentElement.style.setProperty('--rgb',uiRgb.join(','));
 const luma=(uiRgb[0]*299+uiRgb[1]*587+uiRgb[2]*114)/1000;document.documentElement.style.setProperty('--button-ink',luma>148?'#191b1e':'#fff');
 makeSprites();renderLayers();draw(performance.now()/1000);
}
function syncColorModeUI(){
 document.querySelectorAll('.mode-option').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.colorMode===colorMode)));
 $('mixPanel').hidden=colorMode!=='mix';$('sandALabel').textContent=colorMode==='mix'?'砂 A':'砂';
 $('mixRatio').value=String(mixRatio);$('ratioValue').innerHTML=`<b>A ${mixRatio}</b><span>:</span><b>${100-mixRatio} B</b>`;
 document.querySelectorAll('.mix-layout').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.layout===mixLayout)));
}
function setColorMode(mode){
 if(!['single','mix'].includes(mode)||mode===colorMode)return;if(state==='done')reset();colorMode=mode;syncColorModeUI();rebuildField();draw(performance.now()/1000);syncState();
}
function setMixRatio(value){
 mixRatio=clamp(Math.round(Number(value)||0),0,100);syncColorModeUI();assignMixLayout();draw(performance.now()/1000);
}
function setMixLayout(layout){
 if(!['mixed','leftRight','topBottom','stripes3'].includes(layout))return;mixLayout=layout;syncColorModeUI();assignMixLayout();draw(performance.now()/1000);
}

// Audio is synthesized locally with Web Audio. It starts only after a user gesture.
const AudioCtor=window.AudioContext||window.webkitAudioContext;
const SOUND_KEY='oshiglass.soundEnabled',SOUND_STYLE_KEY='oshiglass.soundStyle';
let soundEnabled=(()=>{try{return localStorage.getItem(SOUND_KEY)!=='0';}catch{return true;}})();
let soundStyle=(()=>{try{const v=localStorage.getItem(SOUND_STYLE_KEY);return v==='hard'?'hard':'soft';}catch{return 'soft';}})();
let audioCtx=null,audioMaster=null,sandGain=null,noiseBuffer=null,sandSource=null,sandBP=null,sandLP=null;
let audioLandings=0,audioPassed=0,audioBurstCount=0,audioNextBurst=0,audioFlow=0;
function storeSound(){try{localStorage.setItem(SOUND_KEY,soundEnabled?'1':'0');}catch{}}
function storeSoundStyle(){try{localStorage.setItem(SOUND_STYLE_KEY,soundStyle);}catch{}}
function syncSoundStyleUI(){
 document.querySelectorAll('.sound-style-option').forEach(b=>{b.disabled=!AudioCtor;b.setAttribute('aria-pressed',String(b.dataset.soundStyle===soundStyle));});
}
function applySoundStyle(){
 if(!audioCtx||!sandBP||!sandLP)return;const t=audioCtx.currentTime;
 const hard=soundStyle==='hard';sandBP.frequency.setTargetAtTime(hard?6100:3150,t,.035);sandBP.Q.setTargetAtTime(hard?.82:.58,t,.035);sandLP.frequency.setTargetAtTime(hard?9800:5600,t,.035);
}
function setSoundStyle(style){
 if(style!=='soft'&&style!=='hard'||style===soundStyle)return;soundStyle=style;storeSoundStyle();syncSoundStyleUI();applySoundStyle();
 if(soundEnabled)ensureAudio().then(ok=>{if(ok)grainBurst(3);});
}
function syncSoundButton(){
 const b=$('soundButton');if(!b)return;
 b.disabled=!AudioCtor;b.setAttribute('aria-pressed',String(Boolean(AudioCtor&&soundEnabled)));
 b.setAttribute('aria-label',!AudioCtor?'このブラウザでは音声を利用できません':soundEnabled?'音をオフにする':'音をオンにする');
 b.title=!AudioCtor?'このブラウザでは音声を利用できません':'音をオン / オフ';
}
function makeNoiseBuffer(ctx){
 const len=Math.max(1,Math.floor(ctx.sampleRate*1.25)),buf=ctx.createBuffer(1,len,ctx.sampleRate),data=buf.getChannelData(0);
 let last=0;for(let i=0;i<len;i++){const white=Math.random()*2-1;last=last*.18+white*.82;data[i]=last*.72;}return buf;
}
function ensureAudio(){
 if(!AudioCtor||!soundEnabled)return Promise.resolve(false);
 try{
   if(!audioCtx){
     audioCtx=new AudioCtor();noiseBuffer=makeNoiseBuffer(audioCtx);
     audioMaster=audioCtx.createGain();audioMaster.gain.value=.72;audioMaster.connect(audioCtx.destination);
     sandBP=audioCtx.createBiquadFilter();sandLP=audioCtx.createBiquadFilter();
     sandBP.type='bandpass';sandLP.type='lowpass';
     sandGain=audioCtx.createGain();sandGain.gain.value=0;
     sandSource=audioCtx.createBufferSource();sandSource.buffer=noiseBuffer;sandSource.loop=true;
     sandSource.connect(sandBP);sandBP.connect(sandLP);sandLP.connect(sandGain);sandGain.connect(audioMaster);sandSource.start();applySoundStyle();
   }
   if(audioCtx.state==='suspended')return audioCtx.resume().then(()=>true).catch(()=>false);
   return Promise.resolve(true);
 }catch{return Promise.resolve(false);}
}
function fadeSand(value=.0,time=.08){if(audioCtx&&sandGain){const t=audioCtx.currentTime;sandGain.gain.cancelScheduledValues(t);sandGain.gain.setTargetAtTime(value,t,time);}}
function shortTone(freq,duration,gain=.02,type='sine',delay=0){
 if(!audioCtx||!audioMaster||!soundEnabled)return;
 const t=audioCtx.currentTime+delay,o=audioCtx.createOscillator(),g=audioCtx.createGain();o.type=type;o.frequency.setValueAtTime(freq,t);g.gain.setValueAtTime(.0001,t);g.gain.exponentialRampToValueAtTime(Math.max(.0002,gain),t+.009);g.gain.exponentialRampToValueAtTime(.0001,t+duration);o.connect(g);g.connect(audioMaster);o.start(t);o.stop(t+duration+.03);
}
function glassClink(gain=.007,delay=0,baseFreq=0){
 if(!audioCtx||!audioMaster||!soundEnabled)return;
 const t=audioCtx.currentTime+delay,base=baseFreq||1450+Math.random()*950;
 // Fast attack and inharmonic partials: more bead-on-glass, less musical chime.
 const partials=[[1,1,.074],[2.31,.34,.052],[3.87,.12,.033]];
 for(const [ratio,amp,dur] of partials){
   const o=audioCtx.createOscillator(),g=audioCtx.createGain();o.type='sine';
   o.frequency.setValueAtTime(base*ratio*(.985+Math.random()*.03),t);
   g.gain.setValueAtTime(.0001,t);g.gain.exponentialRampToValueAtTime(Math.max(.00016,gain*amp),t+.0014);g.gain.exponentialRampToValueAtTime(.0001,t+dur);
   o.connect(g);g.connect(audioMaster);o.start(t);o.stop(t+dur+.015);
 }
}
function grainBurst(count=1){
 if(!audioCtx||!audioMaster||!noiseBuffer||!soundEnabled)return;
 const t=audioCtx.currentTime,src=audioCtx.createBufferSource(),hp=audioCtx.createBiquadFilter(),bp=audioCtx.createBiquadFilter(),g=audioCtx.createGain(),hard=soundStyle==='hard';
 src.buffer=noiseBuffer;hp.type='highpass';hp.frequency.value=hard?3900:1350;bp.type='bandpass';bp.frequency.value=hard?6500+Math.random()*1900:2800+Math.random()*950;bp.Q.value=hard?2.15:.75;
 const peak=hard?Math.min(.014,.0028+Math.log1p(count)*.0019):Math.min(.032,.0055+Math.log1p(count)*.0042);
 g.gain.setValueAtTime(.0001,t);g.gain.exponentialRampToValueAtTime(peak,t+(hard?.0011:.004));g.gain.exponentialRampToValueAtTime(.0001,t+(hard?.012:.034));
 src.connect(hp);hp.connect(bp);bp.connect(g);g.connect(audioMaster);src.start(t,Math.random()*.9,hard?.018:.045);src.stop(t+(hard?.023:.05));
 if(hard){
   const hits=Math.min(2,1+Math.floor(Math.log1p(Math.max(1,count))/2.1));
   for(let i=0;i<hits;i++)glassClink(.0042+Math.min(.0032,Math.log1p(count)*.00085),i*.014+Math.random()*.006);
 }
}
function flipSound(){if(soundStyle==='hard'){shortTone(245,.07,.010,'triangle',0);shortTone(175,.055,.006,'triangle',.04);glassClink(.0038,.047,1820);}else{shortTone(190,.09,.018,'triangle',0);shortTone(145,.11,.013,'triangle',.075);}}
function finishSound(){if(soundStyle==='hard'){glassClink(.0072,0,1680);glassClink(.0031,.045,2260);}else{shortTone(710,.32,.016,'sine',0);shortTone(1065,.26,.007,'sine',.018);}}
function updateAudio(t){
 if(!audioCtx||!soundEnabled){return;}
 if(landings<audioLandings||passed<audioPassed){audioLandings=landings;audioPassed=passed;audioBurstCount=0;}
 const dl=Math.max(0,landings-audioLandings),dp=Math.max(0,passed-audioPassed);audioLandings=landings;audioPassed=passed;
 audioBurstCount+=dl;audioFlow=audioFlow*.86+Math.min(1,dl*.13+dp*.07);
 if(audioBurstCount>0&&t>=audioNextBurst){grainBurst(audioBurstCount);audioBurstCount=0;audioNextBurst=t+.052;}
 const remaining=N?clamp((N-passed)/N,0,1):0,tail=clamp(remaining/.14,0,1);
 const active=state==='running'&&passed<N;
 const base=soundStyle==='hard'?(.00065+.0028*tail):(.0045+.0185*tail);
 const target=active?base*(.42+.58*Math.min(1,audioFlow*1.9)):0;
 fadeSand(target,active?.11:.045);
}
function toggleSound(){
 if(!AudioCtor)return;soundEnabled=!soundEnabled;storeSound();syncSoundButton();
 if(soundEnabled){ensureAudio().then(ok=>{if(ok){audioMaster.gain.setTargetAtTime(.72,audioCtx.currentTime,.03);grainBurst(2);}});}
 else if(audioCtx&&audioMaster){fadeSand(0,.025);audioMaster.gain.setTargetAtTime(.0001,audioCtx.currentTime,.025);}
}
function readDuration(){let m=Number($('minutes').value),s=Number($('seconds').value);if(!Number.isFinite(m))m=0;if(!Number.isFinite(s))s=0;return clamp(Math.max(0,Math.floor(m))*60+Math.max(0,Math.floor(s)),10,3600);}
function setDuration(value){duration=clamp(value,10,3600);$('minutes').value=Math.floor(duration/60);$('seconds').value=duration%60;document.querySelectorAll('.preset').forEach(b=>b.setAttribute('aria-pressed',String(+b.dataset.duration===duration)));lastHUD=-1;rebuildField();updateHUD();}
function durationChanged(){if(['running','paused','flipping'].includes(state))return;if(state==='done')reset();duration=readDuration();needsRebuild=true;lastHUD=-1;updateHUD();document.querySelectorAll('.preset').forEach(b=>b.setAttribute('aria-pressed',String(+b.dataset.duration===duration)));const raw=Number($('minutes').value)*60+Number($('seconds').value);$('timeHint').textContent=raw<10?'開始時に10秒に調整します':raw>3600?'開始時に60分に調整します':'長い時間でも、一粒の落下速度は変わりません';}
function updateHUD(){const left=state==='done'?0:Math.max(0,duration-elapsed),second=Math.ceil(left);if(second!==lastHUD){$('clock').textContent=formatTime(left);lastHUD=second;}const percent=state==='done'?100:clamp(elapsed/duration*100,0,100);$('progressFill').style.width=percent+'%';$('progress').setAttribute('aria-valuenow',String(Math.round(percent)));}
function syncState(){
 $('exhibit').dataset.state=state;const running=state==='running',paused=state==='paused',done=state==='done',flip=state==='flipping';
 $('actionLabel').textContent=running?'一時停止':paused?'つづける':flip?'ひっくり返しています':done?'ひっくり返して、もう一度':'反転してスタート';$('actionSymbol').textContent=running?'Ⅱ':paused?'▶':'↻';
 $('statusText').textContent=running?'計測中':paused?'一時停止':flip?'反転中':done?'完了':'準備完了';
 $('clockLabel').textContent=state==='idle'||flip?'設定時間':'残り';
 $('timeHint').textContent=running||paused||flip?'時間を変えるときはリセットしてください':'10秒〜60分 · 粒を小さくすると数が増えます';
 for(const e of document.querySelectorAll('#minutes,#seconds,.preset'))e.disabled=running||paused||flip;
 for(const e of document.querySelectorAll('.shape,#particleTextA,#particleTextB,#grainSize,.mode-option,.mix-layout,#mixRatio'))e.disabled=running||paused||flip;
 $('startButton').disabled=flip;
 const sandDesc=(shape,glyphs)=>shape==='text'?`${glyphs.join('・')}の文字粒`:shape==='star'?'星粒':'丸粒';
 const contentDesc=colorMode==='mix'?`砂A（${sandDesc(shapeA,glyphsA)}）と砂B（${sandDesc(shapeB,glyphsB)}）を${mixRatio}対${100-mixRatio}で配合した`:`${sandDesc(shapeA,glyphsA)}の`;
 canvas.setAttribute('aria-label',`${contentDesc}砂時計。${$('statusText').textContent}。`);
}
function reset(){state='idle';elapsed=carry=simTime=0;accumulator=0;flipProgress=0;frameTurn=0;doneAt=-100;ripples=[];audioLandings=audioPassed=audioBurstCount=0;audioFlow=0;fadeSand(0,.035);$('completeGlow').classList.remove('play');setDuration(readDuration());syncState();}
function finish(){state='done';elapsed=carry=duration;doneAt=performance.now()/1000;settleUntil=doneAt+3;fadeSand(0,.04);finishSound();$('completeGlow').classList.remove('play');void $('completeGlow').offsetWidth;$('completeGlow').classList.add('play');syncState();updateHUD();}
function finishFlip(){
 for(const p of particles){p.x=2*CX-p.x;p.y=2*NECK-p.y;p.px=p.x;p.py=p.y;p.lower=false;p.allowed=false;p.landed=false;p.sleep=false;p.rest=0;p.roll=0;p.supportL=p.supportR=false;p.angle+=Math.PI;}
 frameTurn=(frameTurn+Math.PI)%(2*Math.PI);state='running';simTime=elapsed=carry=0;accumulator=0;passed=granted=landings=0;audioLandings=audioPassed=audioBurstCount=0;audioFlow=0;flipProgress=0;anchor=now();syncState();
}
function startPause(){
 if(state==='flipping')return;
 if(state==='running'){carry=elapsed;state='paused';fadeSand(0,.035);}
 else if(state==='paused'){anchor=now();state='running';if(soundEnabled)ensureAudio();}
 else{state='flipping';flipStarted=now();flipProgress=0;carry=elapsed=simTime=0;accumulator=0;doneAt=-100;ripples=[];$('completeGlow').classList.remove('play');if(soundEnabled)ensureAudio().then(ok=>{if(ok)flipSound();});}
 lastFrame=performance.now();syncState();updateHUD();
}
function frame(timestamp){
 const t=timestamp/1000,delta=Math.max(0,(timestamp-lastFrame)/1000);lastFrame=timestamp;
 if(needsRebuild){needsRebuild=false;rebuildField();syncState();}
 if(state==='flipping'){flipProgress=clamp((now()-flipStarted)/FLIP_TIME,0,1);if(flipProgress>=1)finishFlip();}
 if(state==='running'){
   elapsed=Math.max(0,now()-anchor+carry);
   // A suspended tab resumes the actual bodies. Never reconstruct a pile to
   // simulate elapsed time. Limit catch-up work and carry the physical backlog.
   accumulator+=Math.min(delta,.25);let n=0;
   while(accumulator>=STEP&&n++<24){step(STEP);accumulator-=STEP;}
   if(elapsed>=duration&&passed===N&&particles.every(p=>p.landed))finish();
   if(elapsed>=duration&&state==='running'){$('statusText').textContent='終了処理中';}
 }else if((state==='done'||state==='idle')&&t<settleUntil){accumulator+=Math.min(delta,.05);while(accumulator>=STEP){physics(STEP);accumulator-=STEP;}}
 updateHUD();updateAudio(t);draw(t);requestAnimationFrame(frame);
}
document.querySelectorAll('.swatch').forEach(b=>b.addEventListener('click',()=>setColor(b.dataset.channel,b.dataset.color)));
$('colorPickerA').addEventListener('input',e=>setColor('a',e.target.value));$('colorPickerB').addEventListener('input',e=>setColor('b',e.target.value));
function normalizeHex(value){let v=value.trim().replace(/^#/,'');if(/^[0-9a-fA-F]{3}$/.test(v))v=v.split('').map(c=>c+c).join('');return /^[0-9a-fA-F]{6}$/.test(v)?'#'+v.toLowerCase():null;}
function applyHexField(channel){const id=channel==='a'?'hexColorA':'hexColorB',fallback=channel==='a'?color:colorB,v=normalizeHex($(id).value);if(v)setColor(channel,v);else $(id).value=fallback.toUpperCase();}
for(const channel of ['a','b']){const id=channel==='a'?'hexColorA':'hexColorB',el=$(id);el.addEventListener('input',()=>{const v=normalizeHex(el.value);if(v)setColor(channel,v);});el.addEventListener('change',()=>applyHexField(channel));el.addEventListener('blur',()=>applyHexField(channel));el.addEventListener('keydown',e=>{if(e.key==='Enter'){e.preventDefault();applyHexField(channel);el.blur();}});}
document.querySelectorAll('.mode-option').forEach(b=>b.addEventListener('click',()=>setColorMode(b.dataset.colorMode)));
$('mixRatio').addEventListener('input',e=>setMixRatio(e.target.value));
document.querySelectorAll('.mix-layout').forEach(b=>b.addEventListener('click',()=>setMixLayout(b.dataset.layout)));
document.querySelectorAll('.shape').forEach(b=>b.addEventListener('click',()=>{
 const channel=b.dataset.channel,next=b.dataset.shape,current=channel==='a'?shapeA:shapeB;if(current===next)return;
 if(channel==='a')shapeA=next;else shapeB=next;
 document.querySelectorAll(`.shape[data-channel="${channel}"]`).forEach(s=>s.setAttribute('aria-pressed',String(s===b)));
 if(channel==='b')updateChannelUI('b',colorB);
 $(channel==='a'?'textRowA':'textRowB').hidden=$(channel==='a'?'textHelpA':'textHelpB').hidden=next!=='text';rebuildField();syncState();
}));
function updateText(channel){
 const id=channel==='a'?'particleTextA':'particleTextB',fallback=channel==='a'?'推':'★',e=$(id),v=segments(e.value.replace(/[\r\n\t]/g,'')).slice(0,10).join('');e.value=v;
 if(channel==='a')lettersA=v.trim()||fallback;else lettersB=v.trim()||fallback;rebuildField();syncState();
}
for(const channel of ['a','b']){const id=channel==='a'?'particleTextA':'particleTextB',fallback=channel==='a'?'推':'★',el=$(id);el.addEventListener('input',e=>{if(!e.isComposing)updateText(channel);});el.addEventListener('compositionend',()=>updateText(channel));el.addEventListener('blur',()=>{if(!el.value.trim()){el.value=fallback;updateText(channel);}});}
$('grainSize').addEventListener('input',e=>{sizeSetting=+e.target.value;$('sizeValue').textContent=`${sizeSetting} / 100`;needsRebuild=true;});
document.querySelectorAll('.theme-option').forEach(b=>b.addEventListener('click',()=>setTheme(b.dataset.themeChoice)));
$('minutes').addEventListener('input',durationChanged);$('seconds').addEventListener('input',durationChanged);document.querySelectorAll('.preset').forEach(b=>b.addEventListener('click',()=>{if(state==='done')reset();setDuration(+b.dataset.duration);}));$('startButton').addEventListener('click',startPause);$('resetButton').addEventListener('click',reset);$('soundButton').addEventListener('click',toggleSound);document.querySelectorAll('.sound-style-option').forEach(b=>b.addEventListener('click',()=>setSoundStyle(b.dataset.soundStyle)));
canvas.addEventListener('pointerdown',event=>{
 if(state==='paused'||state==='flipping')return;const rect=canvas.getBoundingClientRect(),x=(event.clientX-rect.left)*W/rect.width,y=(event.clientY-rect.top)*H/rect.height;if(y<TOP||y>FLOOR||Math.abs(x-CX)>halfWidth(y))return;
 ripples.push({x,y,t:performance.now()/1000});if(ripples.length>5)ripples.shift();
 for(const p of particles){const dx=p.x-x,dy=p.y-y,d=Math.hypot(dx,dy);if(d<90){p.sleep=false;p.rest=0;p.px-=dx/(d+1)*(1-d/90)*.45;p.py+=(1-d/90)*.2;}}
 settleUntil=performance.now()/1000+2;
});
document.addEventListener('visibilitychange',()=>{if(document.hidden)fadeSand(0,.025);else lastFrame=performance.now();});
syncThemeUI();updateChannelUI('a',color);updateChannelUI('b',colorB);syncColorModeUI();syncSoundButton();syncSoundStyleUI();rebuildField();syncState();updateHUD();resize();new ResizeObserver(resize).observe(canvas);requestAnimationFrame(frame);
Object.defineProperty(window,'oshiglass',{value:Object.freeze({snapshot(){return{version:'1.0.0',theme,soundEnabled,soundStyle,colorMode,mixRatio,mixLayout,colorA:color,colorB,shapeA,textA:lettersA,glyphsA:[...glyphsA],shapeB,textB:lettersB,glyphsB:[...glyphsB],state,duration,elapsed,simTime,size:sizeSetting,diameter:D,radius:R,total:N,capacity,upper:particles.filter(p=>!p.lower).length,lower:particles.filter(p=>p.lower).length,passed,granted,landings,airborne:particles.filter(p=>p.lower&&!p.landed).length,gravity:G,flipProgress,frameTurn,finite:particles.every(p=>Number.isFinite(p.x+p.y+p.px+p.py)),positions:particles.map(p=>({id:p.id,x:p.x,y:p.y,vx:(p.x-p.px)/STEP,vy:(p.y-p.py)/STEP,r:p.r,lower:p.lower,allowed:p.allowed,landed:p.landed,sleep:p.sleep,glyph:(p.mix===1&&colorMode==='mix'?glyphsB[p.glyph%glyphsB.length]:glyphsA[p.glyph%glyphsA.length]),shade:p.shade,mix:p.mix||0,alpha:1}))};}})});
})();
