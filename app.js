'use strict';
const D=window.DATA;
const $=s=>document.querySelector(s);
const esc=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const T=Object.fromEntries(D.teams.map(t=>[t.id,t]));
const G=D.games.map(g=>({...g,final:g.hs!==null,w:Math.max(1,Math.min(11,Math.floor((Date.parse(g.t.slice(0,10)+'T12:00:00Z')-Date.parse('2026-08-27T12:00:00Z'))/604800000)+1))}));
const BY=Object.fromEntries(G.map(g=>[g.i,g]));
const CLS=['6A','5A D1','5A D2'];
const districts=[...new Set(D.teams.map(t=>key(t)))].sort((a,b)=>CLS.indexOf(a.split('|')[0])-CLS.indexOf(b.split('|')[0])||Number(a.split('|')[1])-Number(b.split('|')[1]));
const local=t=>!!t;
const inArea=t=>area==='all'||(area==='i35'?t.a!=='T':t.r===area);
const allowed=g=>true;
const pickGames=G.filter(g=>!g.final&&allowed(g));
const picks={},scores={},scoreDrafts={};
const wkOf=d=>Math.max(1,Math.min(11,Math.floor((Date.parse(d+'T12:00:00Z')-Date.parse('2026-08-27T12:00:00Z'))/604800000)+1));
const NOW=wkOf(D.asOf),NEXT=Math.min(11,NOW+1);
const PAGE=240;let shown=PAGE,showEarlier=false;let area='all',cls='all',district='all',school='all',hideOutside=true,view='games',week=NEXT,theme='dark';
let standings={},baseStandings={},rankings={},baseRanks={},toastTimer,undo=null;
const ratings=Object.fromEntries([...new Set(G.flatMap(g=>[g.h,g.a]))].map(id=>[id,1500]));
for(const g of G.filter(g=>g.final&&g.hs!==g.as_)){
  const ph=1/(1+10**((ratings[g.a]-ratings[g.h]-(g.nu?0:35))/400));
  const delta=25*(Math.log(Math.abs(g.hs-g.as_)+1)/3+0.4)*((g.hs>g.as_?1:0)-ph);
  ratings[g.h]+=delta;ratings[g.a]-=delta;
}
function key(t){return t.k+'|'+t.d}
function dk(k){const [c,d]=k.split('|');return c+' · District '+d}
function team(id){return T[id]||{id,n:D.guests[id]?.n||'Unknown opponent',c:D.guests[id]?.c||'',m:'',a:'X',k:D.guests[id]?.k||'',c1:'#617068',c2:'#d2d4ce'}}
function date(d,opt){return new Date(d.slice(0,10)+'T12:00:00Z').toLocaleDateString('en-US',opt)}
function shortDate(d){return date(d,{month:'short',day:'numeric'})}
function ft(g){if(g.t.slice(11,16)==='00:00')return 'Time TBA';let [hh,mm]=g.t.slice(11,16).split(':').map(Number);return (hh%12||12)+(mm?':'+String(mm).padStart(2,'0'):'')+(hh>=12?'p':'a')}
function record(s,d=false){const r=d?s.dr:s.r;return r[0]+'–'+r[1]+(r[2]?'–'+r[2]:'')}
function matching(t){if(!t)return false;if(district!=='all')return key(t)===district&&(school==='all'||t.id===school);return inArea(t)&&(cls==='all'||t.k===cls)&&(school==='all'||t.id===school)}
function matchesBase(g){return allowed(g)&&(matching(T[g.h])||matching(T[g.a]))}
function matches(g){return matchesBase(g)&&!(hideOutside&&(!T[g.h]||!T[g.a]))}
function visibleGames(){return G.filter(g=>matches(g)&&(week===0||g.w===week))}
function hiddenCount(){return hideOutside?G.filter(g=>matchesBase(g)&&(!T[g.h]||!T[g.a])&&(week===0||g.w===week)).length:0}
function relevantDistricts(){return districts.filter(k=>D.teams.some(t=>key(t)===k&&matching(t)))}
function compute(withPicks){
  const S=Object.fromEntries(D.teams.map(t=>[t.id,{r:[0,0,0],dr:[0,0,0],pf:0,pa:0,left:0,dp:0,picked:0,h2h:{}}]));
  for(const g of G){
    let winner=g.final?(g.hs>g.as_?g.h:g.hs<g.as_?g.a:'tie'):(withPicks?picks[g.i]:undefined);
    for(const [id,opp,sc,sa] of [[g.h,g.a,g.hs,g.as_],[g.a,g.h,g.as_,g.hs]]){
      if(!S[id])continue;const s=S[id];
      if(!winner){s.left++;if(g.d)s.dp++;continue}
      const idx=winner==='tie'?2:winner===id?0:1;s.r[idx]++;
      if(g.final){s.pf+=sc;s.pa+=sa}else{s.picked++}
      if(g.d){s.dr[idx]++;s.h2h[opp]=idx===0?1:idx===1?-1:0}
    }
  }
  return S;
}
function pct(r){const n=r.reduce((a,b)=>a+b,0);return n?(r[0]+r[2]/2)/n:0}
function ranked(S,k){
  const ids=D.teams.filter(t=>key(t)===k).map(t=>t.id);
  const buckets=new Map();
  ids.sort((a,b)=>pct(S[b].dr)-pct(S[a].dr)||S[b].dr[0]-S[a].dr[0]);
  for(const id of ids){const p=pct(S[id].dr)+'|'+S[id].dr[0];if(!buckets.has(p))buckets.set(p,[]);buckets.get(p).push(id)}
  const out=[];out.tied=new Set();
  for(const b of buckets.values()){
    if(b.length===2&&S[b[0]].h2h[b[1]]){if(S[b[0]].h2h[b[1]]===-1)b.reverse()}
    else if(b.length>1){
      const sweeper=b.find(id=>b.every(o=>o===id||S[id].h2h[o]===1));
      b.sort((a,b)=>T[a].n.localeCompare(T[b].n));
      if(sweeper){b.splice(b.indexOf(sweeper),1);b.unshift(sweeper)}
      b.forEach(id=>{if(id!==sweeper)out.tied.add(id)});
    }
    out.push(...b);
  }
  return out;
}
function status(k){
  const ids=rankings[k],S=standings,res={};
  const w=id=>S[id].dr[0]+S[id].dr[2]/2,mx=id=>w(id)+S[id].dp;
  const done=ids.every(id=>S[id].dp===0);
  ids.forEach((id,i)=>{
    if(done){res[id]=i<4?'in':'out';return}
    const above=ids.filter(o=>o!==id&&mx(o)>=w(id)).length,below=ids.filter(o=>o!==id&&w(o)>mx(id)).length;
    if(above<=3)res[id]='in';else if(below>=4)res[id]='out';
  });
  return res;
}
function stTag(v,done){return v==='in'?'<span class="st x">'+(done?'In':'Clinched')+'</span>':v==='out'?'<span class="st e">'+(done?'Out':'Eliminated')+'</span>':''}
function recalc(){standings=compute(true);rankings=Object.fromEntries(districts.map(k=>[k,ranked(standings,k)]))}
baseStandings=compute(false);baseRanks=Object.fromEntries(districts.map(k=>[k,ranked(baseStandings,k)]));recalc();
function strength(g){return 1/(1+10**((ratings[g.a]-ratings[g.h]-(g.nu?0:35))/400))}
function chances(g){const h=Math.round(strength(g)*100);return {h,a:100-h}}
function replaceState(target,next){for(const id of Object.keys(target))delete target[id];Object.assign(target,next)}
function remember(){undo={picks:{...picks},scores:structuredClone(scores),drafts:structuredClone(scoreDrafts)}}
function toast(msg,canUndo=false){
  clearTimeout(toastTimer);const e=$('#toast');e.hidden=false;e.innerHTML='<span>'+esc(msg)+'</span>'+(canUndo?'<button type="button" id="undoBtn">Undo</button>':'');
  if(canUndo)$('#undoBtn').onclick=()=>{replaceState(picks,undo?.picks||{});replaceState(scores,undo?.scores||{});replaceState(scoreDrafts,undo?.drafts||{});recalc();render();toast('Previous predictions restored')};
  toastTimer=setTimeout(()=>e.hidden=true,5000);
}
function updateHead(){
  const games=visibleGames(),open=games.filter(g=>!g.final),done=open.filter(g=>picks[g.i]).length,el=$('#gcount');
  if(el)el.textContent=games.length+' games · '+done+' / '+open.length+' open games picked';
}
function refreshGames(g){
  if(view!=='games'){renderMain();return}
  const ids=new Set([g.h,g.a]);
  for(const el of document.querySelectorAll('.game')){
    const x=BY[el.dataset.game];
    if(x&&!x.final&&(ids.has(x.h)||ids.has(x.a)))el.outerHTML=card(x);
  }
  updateHead();
}
function pick(id,who){
  const g=BY[id];if(!g||g.final)return;
  if(picks[id]===who){delete picks[id];delete scores[id];delete scoreDrafts[id]}
  else {picks[id]=who;if(scores[id]&&(scores[id].h>scores[id].a?g.h:g.a)!==who){delete scores[id];delete scoreDrafts[id]}}
  recalc();refreshGames(g);progress();document.querySelector('[data-pick="'+id+'"][data-who="'+who+'"]')?.focus({preventScroll:true});
}
function scoreError(form,msg,field){
  const note=form.querySelector('.score-note');note.textContent=msg;note.classList.add('error');
  for(const input of form.querySelectorAll('input'))input.setAttribute('aria-invalid',String(!field||input===field));
  (field||form.querySelector('input')).focus({preventScroll:true});
}
function saveScore(form){
  const g=BY[form.dataset.scoreForm];if(!g||g.final)return;
  const vals={},inputs=[...form.querySelectorAll('[data-score-side]')];
  for(const input of inputs){
    const value=input.value.trim();
    if(!/^\d{1,3}$/.test(value)||Number(value)>199){scoreError(form,'Enter a whole-number score from 0 to 199 for both teams.',input);return}
    vals[input.dataset.scoreSide]=Number(value);
  }
  if(vals.a===vals.h){scoreError(form,'Choose different final scores so there is a winner.');return}
  remember();scores[g.i]=vals;scoreDrafts[g.i]={a:String(vals.a),h:String(vals.h)};picks[g.i]=vals.h>vals.a?g.h:g.a;
  recalc();refreshGames(g);progress();document.querySelector('[data-score-form="'+g.i+'"] button[type=submit]')?.focus({preventScroll:true});
}
function clearScore(id){
  remember();delete scores[id];delete scoreDrafts[id];refreshGames(BY[id]);
  document.querySelector('[data-score-form="'+id+'"] input')?.focus({preventScroll:true});
}
function progress(){
  const n=Object.keys(picks).length,tot=pickGames.length;
  $('#progressText').textContent=n+' / '+tot+' picks';$('#progressBar').style.width=(tot?n/tot*100:0)+'%';
}
function seg(sel,vals,current,fn){$(sel).innerHTML=vals.map(([v,l])=>'<button type="button" aria-pressed="'+(current===v)+'" data-val="'+v+'">'+l+'</button>').join('');$(sel).onclick=e=>{const b=e.target.closest('[data-val]');if(b)fn(b.dataset.val)}}
function filterRender(){
  seg('#areaSeg',[['all','All Texas'],['i35','Austin–San Antonio'],['I','Region I'],['II','Region II'],['III','Region III'],['IV','Region IV']],area,v=>{area=v;district='all';school='all';render()});
  seg('#classSeg',[['all','All'],['6A','6A'],['5A D1','5A D1'],['5A D2','5A D2']],cls,v=>{cls=v;district='all';school='all';render()});
  const options=districts.filter(k=>D.teams.some(t=>key(t)===k&&inArea(t)&&(cls==='all'||t.k===cls)));
  $('#districtSel').innerHTML='<option value="all">All districts</option>'+options.map(k=>'<option value="'+k+'"'+(district===k?' selected':'')+'>'+dk(k)+'</option>').join('');
  const schools=D.teams.filter(t=>inArea(t)&&(cls==='all'||t.k===cls)&&(district==='all'||key(t)===district)).sort((a,b)=>a.n.localeCompare(b.n));
  $('#teamList').innerHTML=schools.map(t=>'<option value="'+esc(t.n)+'"></option>').join('');
  $('#teamIn').value=school==='all'?'':T[school].n;
  $('#hideOutside').checked=hideOutside;
}
function render(){shown=PAGE;showEarlier=false;filterRender();renderMain();progress()}
function renderMain(){
  const main=$('#main');
  if(view==='games')renderGames(main);else if(view==='standings')renderStandings(main);else renderPlayoffs(main);
}
function dot(t){return '<i class="dot" style="background:linear-gradient(135deg,'+t.c1+' 50%,'+(t.c2||t.c1)+' 50%)" aria-hidden="true"></i>'}
function side(g,id,home){
  const t=team(id),actual=baseStandings[id],projected=standings[id],win=g.final&&((home?g.hs:g.as_)>(home?g.as_:g.hs)),lose=g.final&&((home?g.hs:g.as_)<(home?g.as_:g.hs)),picked=picks[g.i]===id;
  const location=g.nu?'Neutral site':home?'Home':'Away';
  const nw=x=>'<span class="nw">'+x+'</span>',recordHtml=actual?nw('Current '+record(actual))+' · '+nw('District '+record(actual,true)):'';
  const future=!g.final&&projected?.picked?'<span class="rec projected">'+nw('With your picks: '+record(projected))+' · '+nw('District '+record(projected,true))+'</span>':'';
  const body=dot(t)+'<span class="who"><span class="nm">'+esc(t.n)+'</span><span class="rec">'+esc(location+(!T[id]?' · '+(t.k||'Other')+' · outside list':''))+'</span>'+(recordHtml?'<span class="rec">'+recordHtml+'</span>':'')+future+'</span>';
  if(g.final)return '<div class="side locked '+(win?'won':lose?'lost':'')+'">'+body+'<span class="score">'+(home?g.hs:g.as_)+'</span></div>';
  const c=chances(g),p=home?c.h:c.a,favorite=p>50;
  const odds='<span class="res"><b class="win-chance">'+p+'% win</b><span>'+(100-p)+'% loss</span>'+(favorite?'<span class="favorite">Favorite</span>':p===50?'<span>Even match</span>':'')+(picked?'<span class="pickmark">Your pick</span>':'')+'</span>';
  return '<button type="button" class="side '+(picked?'pick':'')+'" data-pick="'+g.i+'" data-who="'+esc(id)+'" aria-pressed="'+picked+'" aria-label="Pick '+esc(t.n)+' to win. Estimated '+p+' percent win chance'+(picked?', currently selected':'')+'">'+body+odds+'</button>';
}
function scoreForm(g){
  if(g.final)return '<p class="final-note">Final score locked · Predictions closed</p>';
  const saved=scores[g.i],draft=scoreDrafts[g.i]||saved||{},id=g.i;
  const field=(side,label)=>'<label class="score-field" for="score-'+id+'-'+side+'"><span>'+esc(team(g[side]).n)+'</span><input id="score-'+id+'-'+side+'" type="number" inputmode="numeric" min="0" max="199" step="1" placeholder="—" value="'+esc(draft[side]??'')+'" data-score-side="'+side+'" data-testid="score-'+side+'-'+id+'" aria-label="Predicted score for '+esc(team(g[side]).n)+'" aria-describedby="score-note-'+id+'"><small>'+label+'</small></label>';
  let msg='Optional · Saving scores selects your winner.';
  if(saved)msg='Saved: '+team(g.a).n+' '+saved.a+' – '+team(g.h).n+' '+saved.h;
  return '<form class="score-form" data-score-form="'+id+'" novalidate><fieldset><legend>Your score prediction</legend><div class="score-fields">'+field('a',g.nu?'Neutral':'Away')+'<span class="score-dash" aria-hidden="true">–</span>'+field('h',g.nu?'Neutral':'Home')+'</div></fieldset><div class="score-actions"><button class="btn score-save" type="submit" data-testid="save-score-'+id+'">'+(saved?'Update score':'Save score')+'</button><button class="btn ghost score-clear" type="button" data-clear-score="'+id+'" '+(!saved&&draft.a===undefined&&draft.h===undefined?'hidden':'')+'>Clear score</button></div><p class="score-note" id="score-note-'+id+'" role="status">'+esc(msg)+'</p></form>';
}
function card(g){
  const k=T[g.h]?key(T[g.h]):key(T[g.a]);
  const tag=g.d?'<span class="tag dist">'+esc(dk(k))+'</span>':'<span class="tag">Non-district</span>';
  return '<article class="game" data-game="'+g.i+'"><div class="g-meta"><span>'+ft(g)+(g.t.slice(11,16)==='00:00'?'':' local time')+'</span><span class="tags">'+tag+(g.final?'<span class="tag final">Final</span>':'')+'</span></div>'+side(g,g.a,false)+side(g,g.h,true)+scoreForm(g)+'</article>';
}
function weekRange(w){const a=new Date(Date.parse('2026-08-27T12:00Z')+(w-1)*604800000);return shortDate(a.toISOString())+'–'+new Date(a.getTime()+172800000).getUTCDate()}
function renderGames(el){
  const games=visibleGames(),open=games.filter(g=>!g.final),done=open.filter(g=>picks[g.i]).length;
  const name=school!=='all'?T[school].n:district!=='all'?dk(district)+(week===0?'':' · Week '+week):(week===0?'All games':'Week '+week+' games');
  let out='<div class="head-row"><div><h1 class="page-title">'+esc(name)+'</h1><p class="page-sub">Pick a winner or enter your predicted final score below the game.</p></div><span class="muted" id="gcount">'+games.length+' games · '+done+' / '+open.length+' open games picked</span></div>';
  out+='<nav class="weeks" aria-label="Select week"><button type="button" class="wk" data-week="0" aria-pressed="'+(week===0)+'"><b>All weeks</b><span>Full season</span></button>';
  for(let w=1;w<=11;w++){
    const start=new Date(Date.parse('2026-08-27T12:00Z')+(w-1)*604800000).toISOString();
    out+='<button type="button" class="wk '+(w===NOW?'now':'')+'" data-week="'+w+'" aria-pressed="'+(week===w)+'"><b>Week '+w+'</b><span>'+shortDate(start)+'–'+new Date(Date.parse(start)+172800000).getUTCDate()+'</span></button>';
  }
  out+='</nav>';
  const hid=hiddenCount();
  out+='<p class="muted" style="font-size:var(--text-xs);margin:var(--s2) 0 var(--s4)">2026 season · Final scores are locked · Win/loss percentages are model estimates from recorded results, not official odds · Records are current as of '+shortDate(D.asOf)+' · Your scores do not change the estimated chances'+(hid?' · <button type="button" class="linkbtn" data-showoutside>Show '+hid+' game'+(hid>1?'s':'')+' vs. schools outside the list</button>':'')+'</p>';
  if(!games.length)out+='<div class="empty"><b>No games match these filters.</b>Try another week or clear the school and district filters.</div>';
  const ordered=[...games].sort((a,b)=>(week===0?a.w-b.w:0)||a.t.slice(0,10).localeCompare(b.t.slice(0,10))||a.t.localeCompare(b.t)||(a.final-b.final)||team(a.h).n.localeCompare(team(b.h).n));
  const firstOpen=ordered.findIndex(g=>!g.final),skip=(week===0&&!showEarlier&&school==='all'&&district==='all'&&firstOpen>0)?firstOpen:0;
  if(skip)out+='<div class="more earlier"><button type="button" class="btn ghost" data-earlier>Show '+skip+' earlier final games</button></div>';
  const slice=week===0?ordered.slice(skip,skip+shown):ordered;
  const grp={};for(const g of slice){const k=week===0?'w'+String(g.w).padStart(2,'0'):g.t.slice(0,10);(grp[k]??=[]).push(g)}
  for(const [k,gs] of Object.entries(grp).sort()){
    const title=week===0?'Week '+Number(k.slice(1))+' · '+weekRange(Number(k.slice(1))):date(k,{weekday:'long',month:'long',day:'numeric'});
    out+='<section aria-label=\"'+esc(title)+'\"><h2 class=\"day\">'+esc(title)+'</h2><div class=\"grid\">'+gs.map(card).join('')+'</div></section>';
  }
  if(week===0&&ordered.length-skip>shown)out+='<div class=\"more\"><button type=\"button\" class=\"btn\" data-more>Show '+Math.min(PAGE,ordered.length-skip-shown)+' more games · '+(ordered.length-skip-shown)+' not shown yet</button></div>';
  el.innerHTML=out;
  el.onclick=e=>{const p=e.target.closest('[data-pick]'),w=e.target.closest('[data-week]'),clear=e.target.closest('[data-clear-score]');if(e.target.closest('[data-earlier]')){showEarlier=true;renderMain()}else if(e.target.closest('[data-more]')){shown+=PAGE;renderMain()}else if(clear)clearScore(clear.dataset.clearScore);else if(e.target.closest('[data-showoutside]')){hideOutside=false;render()}else if(p)pick(p.dataset.pick,p.dataset.who);else if(w){week=Number(w.dataset.week);shown=PAGE;showEarlier=false;renderMain()}};
  el.onsubmit=e=>{const form=e.target.closest('[data-score-form]');if(form){e.preventDefault();saveScore(form)}};
  el.oninput=e=>{
    const input=e.target.closest('[data-score-side]');if(!input)return;
    const form=input.closest('[data-score-form]'),id=form.dataset.scoreForm;
    scoreDrafts[id]=Object.fromEntries([...form.querySelectorAll('[data-score-side]')].map(i=>[i.dataset.scoreSide,i.value]));
    form.querySelector('.score-clear').hidden=false;
    const note=form.querySelector('.score-note');note.classList.remove('error');note.textContent='Not saved yet · Save score to apply your prediction.';
    for(const i of form.querySelectorAll('input'))i.removeAttribute('aria-invalid');
  };
}
function schoolJump(id){
  area='all';cls='all';district='all';school=id;week=0;view='games';tabRender();render();$('#main').scrollIntoView({behavior:'smooth',block:'start'});
}
function tableCard(k){
  const ids=rankings[k],b=baseRanks[k],has=ids.some(id=>standings[id].picked),stt=status(k),fin=ids.every(id=>standings[id].dp===0);
  let out='<section class="dcard"><header><h3>'+esc(dk(k))+'</h3><span>Region '+T[ids[0]].r+(has?' · Predicted':' · Current')+'</span></header><table class="tbl"><thead><tr><th>#</th><th>School</th><th title="District record">Dist.</th><th title="Overall record">Overall</th><th class="hide-s" title="Unpicked district games left">Left</th></tr></thead><tbody>';
  ids.forEach((id,i)=>{const t=T[id],s=standings[id],move=b.indexOf(id)-i;
    out+='<tr class="'+(i<4?'in ':'')+(i===4?'cut ':'')+'"><td>'+String(i+1).padStart(2,'0')+'</td><td><button type="button" class="tname" data-school="'+id+'"'+'>'+dot(t)+'<span class="t-n">'+esc(t.n)+'</span>'+stTag(stt[id],fin)+(ids.tied.has(id)?'<span class="st" title="Tied on district record; tiebreaker not resolved">Tied</span>':'')+(move?'<span class="mv '+(move>0?'up':'dn')+'" title="Rank change from current standings">'+(move>0?'↑':'↓')+Math.abs(move)+'</span>':'')+'</button></td><td><span>'+record(s,true)+'</span></td><td><span>'+record(s)+'</span></td><td class="hide-s"><span>'+s.dp+'</span></td></tr>';
  });
  return out+'</tbody></table></section>';
}
function renderStandings(el){
  const ks=relevantDistricts();
  el.innerHTML='<div class="head-row"><div><h1 class="page-title">District standings</h1><p class="page-sub">Your picks update the records and district order immediately.</p></div><span class="muted">'+ks.length+(ks.length===1?' district':' districts')+'</span></div><div class="legend"><span>Top-four playoff line</span><span class="p">↑ ↓ Rank change from current standings</span></div><p class="muted" style="font-size:var(--text-xs);margin:0 0 var(--s5)">Ranked by district winning percentage, then head-to-head. Teams tied on record with no head-to-head winner are marked “Tied” and listed alphabetically; the real tiebreaker is set by each district. </p><div class="cards">'+ks.map(tableCard).join('')+'</div>';
  el.onclick=e=>{const b=e.target.closest('[data-school]');if(b)schoolJump(b.dataset.school)};
}
function pcard(k){
  const ids=rankings[k],b=baseRanks[k];
  let out='<section class="pcard"><h3>District '+k.split('|')[1]+' <span>Region '+T[ids[0]].r+'</span></h3>';
  ids.slice(0,6).forEach((id,i)=>{
    const t=T[id],s=standings[id],now=i<4,was=b.indexOf(id)<4;
    if(i===4)out+='<hr class="divider">';
    out+='<button type="button" class="seed '+(i>=4?'bubble':'')+'" data-school="'+id+'"'+'><span class="n">'+(i+1)+'</span>'+dot(t)+'<span class="t-n">'+esc(t.n)+'</span>'+(now&&!was?'<span class="chg in">MOVED IN</span>':!now&&was?'<span class="chg out">MOVED OUT</span>':'')+(ids.tied.has(id)?'<span class="st">Tied</span>':'')+'<small>'+record(s,true)+'</small></button>';
  });
  return out+'</section>';
}
function renderPlayoffs(el){
  const ks=relevantDistricts();let inNow=0,added=0,dropped=0;
  for(const k of ks){const a=rankings[k].slice(0,4),b=baseRanks[k].slice(0,4);inNow+=a.length;added+=a.filter(id=>!b.includes(id)).length;dropped+=b.filter(id=>!a.includes(id)).length}
  let out='<div class="head-row"><div><h1 class="page-title">Playoff picture</h1><p class="page-sub">Projected district qualifiers, based on the games you’ve picked so far.</p></div></div><div class="summary"><div class="stat"><b>'+inNow+'</b><span>Teams in a top-four spot</span></div><div class="stat"><b class="pos">'+added+'</b><span>Moved into a playoff spot</span></div><div class="stat"><b>'+dropped+'</b><span>Moved out of a playoff spot</span></div></div><p class="muted" style="font-size:var(--text-xs);margin:0 0 var(--s5)">Top four qualify. The next two are shown below the dashed line. This is a qualifier view, not a seeded statewide bracket. 6A qualifiers split into Division I / II by enrollment; that split is not implemented yet. Unresolved district ties remain provisional.</p>';
  for(const c of ['6A','5A D1','5A D2']){
    const kk=ks.filter(k=>k.startsWith(c+'|'));if(!kk.length)continue;
    out+='<section class="grp"><h2>'+c+' <small>'+kk.length+' districts</small></h2><div class="pgrid">'+kk.map(pcard).join('')+'</div></section>';
  }
  el.innerHTML=out;el.onclick=e=>{const b=e.target.closest('[data-school]');if(b)schoolJump(b.dataset.school)};
}
function tabRender(){for(const b of $('#tabs').children)b.setAttribute('aria-selected',String(b.dataset.view===view))}
// TX2 codes include winner picks and saved scores; legacy I35 codes still load.
const signature=(()=>{let n=0;for(const c of pickGames.map(g=>g.i).join(''))n=(n*31+c.charCodeAt(0))>>>0;return n.toString(36)})();
const pack64=str=>btoa(str).replace(/\+/g,'-').replace(/\//g,'_').replace(/=+$/,'');
const unpack64=str=>{if(!/^[A-Za-z0-9_-]+$/.test(str))throw Error('Invalid code format.');return atob(str.replace(/-/g,'+').replace(/_/g,'/'))};
function packedPicks(){const bytes=[];for(let i=0;i<pickGames.length;i+=4){let n=0;for(let j=0;j<4&&i+j<pickGames.length;j++){const g=pickGames[i+j];n|=(picks[g.i]===g.h?1:picks[g.i]===g.a?2:0)<<(j*2)}bytes.push(n)}return pack64(String.fromCharCode(...bytes))}
function encode(){return 'TX2.'+signature+'.'+pack64(JSON.stringify({p:packedPicks(),s:pickGames.flatMap((g,i)=>scores[g.i]?[[i,scores[g.i].a,scores[g.i].h]]:[])}))}
function decode(code){
  const a=code.trim().split('.');if(a.length!==3||!['I35','TX2'].includes(a[0])||a[1]!==signature)throw Error('This code is not for the current schedule.');
  let payload=a[0]==='TX2'?JSON.parse(unpack64(a[2])):{p:a[2],s:[]};
  if(!payload||typeof payload.p!=='string'||!Array.isArray(payload.s)||payload.s.length>pickGames.length)throw Error('Invalid predictions in code.');
  const str=unpack64(payload.p);if(str.length!==Math.ceil(pickGames.length/4))throw Error('This code is incomplete.');
  const next={},nextScores={};
  for(let i=0;i<pickGames.length;i++){const n=(str.charCodeAt(Math.floor(i/4))>>((i%4)*2))&3;if(n===3)throw Error('Invalid pick in code.');const g=pickGames[i];if(n)next[g.i]=n===1?g.h:g.a}
  for(const entry of payload.s){
    if(!Array.isArray(entry)||entry.length!==3)throw Error('Invalid score in code.');
    const [i,away,home]=entry;
    if(!Number.isInteger(i)||i<0||i>=pickGames.length||![away,home].every(v=>Number.isInteger(v)&&v>=0&&v<=199)||away===home)throw Error('Invalid score in code.');
    const g=pickGames[i];if(nextScores[g.i]||next[g.i]!== (home>away?g.h:g.a))throw Error('Score and winner do not match in code.');
    nextScores[g.i]={a:away,h:home};
  }
  return {picks:next,scores:nextScores};
}
$('#districtSel').onchange=e=>{district=e.target.value;school='all';render()};
$('#teamIn').onchange=e=>{const v=e.target.value.trim().toLowerCase();if(!v){if(school!=='all'){school='all';render()}return}
  if(school!=='all'&&T[school].n.toLowerCase()===v)return;
  const hit=D.teams.find(t=>t.n.toLowerCase()===v)||D.teams.find(t=>t.n.toLowerCase().includes(v)&&inArea(t)&&(cls==='all'||t.k===cls));
  if(hit){school=hit.id;district='all';area='all';cls='all';week=0;render()}else{e.target.value=school==='all'?'':T[school].n;toast('No school matches “'+e.target.value+'”.')}};
$('#hideOutside').onchange=e=>{hideOutside=e.target.checked;renderMain()};
$('#tabs').onclick=e=>{const b=e.target.closest('[data-view]');if(b){view=b.dataset.view;tabRender();renderMain()}};
$('#themeBtn').onclick=()=>{theme=theme==='dark'?'light':'dark';document.documentElement.dataset.theme=theme;$('#themeBtn').textContent=theme==='dark'?'Light':'Dark'};
$('#autoBtn').onclick=()=>{const e=$('#autoMenu');e.hidden=!e.hidden;$('#autoBtn').setAttribute('aria-expanded',String(!e.hidden))};
$('#autoMenu').onclick=e=>{
  const b=e.target.closest('[data-auto]');if(!b)return;
  const mode=b.dataset.auto,list=(mode==='view'?visibleGames():pickGames).filter(g=>!g.final&&!picks[g.i]);
  if(!list.length){toast('No open games left to pick.');return}
  remember();for(const g of list){const p=strength(g);picks[g.i]=(mode==='rand'?Math.random()<p:p>=.5)?g.h:g.a}
  $('#autoMenu').hidden=true;$('#autoBtn').setAttribute('aria-expanded','false');recalc();render();toast(list.length+' winners picked',true);
};
document.addEventListener('click',e=>{if(!e.target.closest('#autoMenu')&&!e.target.closest('#autoBtn')){$('#autoMenu').hidden=true;$('#autoBtn').setAttribute('aria-expanded','false')}});
document.addEventListener('keydown',e=>{if(e.key==='Escape'){$('#autoMenu').hidden=true;$('#autoBtn').setAttribute('aria-expanded','false')}});
$('#resetBtn').onclick=()=>{const n=Object.keys(picks).length;if(!n&&!Object.keys(scores).length&&!Object.keys(scoreDrafts).length){toast('There are no predictions to reset.');return}remember();replaceState(picks,{});replaceState(scores,{});replaceState(scoreDrafts,{});recalc();render();toast('Winner and score predictions cleared',true)};
$('#shareBtn').onclick=()=>{$('#codeOut').value=encode();$('#codeIn').value='';$('#copyMsg').textContent='';$('#loadMsg').textContent='';$('#shareDlg').showModal()};
$('#copyBtn').onclick=async()=>{try{await navigator.clipboard.writeText($('#codeOut').value);$('#copyMsg').textContent='Copied.'}catch{$('#codeOut').focus();$('#codeOut').select();$('#copyMsg').textContent='Selected — press Ctrl+C or ⌘C to copy.'}};
$('#loadBtn').onclick=()=>{try{const next=decode($('#codeIn').value);remember();replaceState(picks,next.picks);replaceState(scores,next.scores);replaceState(scoreDrafts,{});recalc();render();$('#shareDlg').close();toast(Object.keys(next.picks).length+' winners and '+Object.keys(next.scores).length+' scores loaded',true)}catch(e){$('#loadMsg').textContent=e.message||'Could not read that code.'}};
$('#asOf').textContent=date(D.asOf,{month:'long',day:'numeric',year:'numeric'});
$('.brand').onclick=e=>{e.preventDefault();area='all';cls='all';district='all';school='all';week=NEXT;view='games';tabRender();render();window.scrollTo({top:0,behavior:'smooth'})};
render();
window.predictor={T,G,picks,scores,scoreDrafts,chances,standings:()=>standings,rankings:()=>rankings,pickGames,encode,decode,compute,ranked};
