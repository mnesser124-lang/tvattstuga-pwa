function qrcode(typeNumber,errorCorrectionLevel){
  // Offline QR encoder, Version 1-L, optimized for the app's TVATT-XXXX payload.
  // Uses QR Alphanumeric mode and standard Reed-Solomon error correction.
  const ALPHA='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:';
  const EXP=new Array(256), LOG=new Array(256);
  let x=1;
  for(let i=0;i<255;i++){EXP[i]=x;LOG[x]=i;x<<=1;if(x&0x100)x^=0x11d;}
  EXP[255]=EXP[0];
  const gfMul=(a,b)=>(a===0||b===0)?0:EXP[(LOG[a]+LOG[b])%255];
  function addBits(arr,val,n){for(let i=n-1;i>=0;i--)arr.push((val>>i)&1);}
  function rsEncode(data,ecCount){
    let gen=[1];
    for(let i=0;i<ecCount;i++){
      const out=new Array(gen.length+1).fill(0),g=EXP[i];
      for(let j=0;j<gen.length;j++){out[j]^=gen[j];out[j+1]^=gfMul(gen[j],g);}
      gen=out;
    }
    const msg=data.slice();for(let i=0;i<ecCount;i++)msg.push(0);
    for(let i=0;i<data.length;i++){
      const f=msg[i];if(!f)continue;
      for(let j=0;j<gen.length;j++)msg[i+j]^=gfMul(gen[j],f);
    }
    return data.concat(msg.slice(-ecCount));
  }
  function dataCodewords(text){
    const s=String(text||'').toUpperCase();
    if(s.length>25)throw new Error('QR-text-too-long');
    for(const ch of s)if(ALPHA.indexOf(ch)<0)throw new Error('QR-unsupported-character');
    const bits=[];addBits(bits,0b0010,4);addBits(bits,s.length,9);
    for(let i=0;i+1<s.length;i+=2)addBits(bits,ALPHA.indexOf(s[i])*45+ALPHA.indexOf(s[i+1]),11);
    if(s.length%2)addBits(bits,ALPHA.indexOf(s[s.length-1]),6);
    const room=19*8;for(let i=0;i<Math.min(4,room-bits.length);i++)bits.push(0);
    while(bits.length%8)bits.push(0);
    const out=[];for(let i=0;i<bits.length;i+=8){let v=0;for(let j=0;j<8;j++)v=(v<<1)|(bits[i+j]||0);out.push(v);}
    let pad=0;while(out.length<19)out.push(pad++%2===0?0xEC:0x11);
    return rsEncode(out,7);
  }
  function bchTypeInfo(data){
    let d=data<<10,g=0x537;while((d.toString(2).length-g.toString(2).length)>=0)d^=g<<(d.toString(2).length-g.toString(2).length);
    return ((data<<10)|d)^0x5412;
  }
  function mask(m,r,c){switch(m){
    case 0:return (r+c)%2===0;case 1:return r%2===0;case 2:return c%3===0;case 3:return (r+c)%3===0;
    case 4:return (Math.floor(r/2)+Math.floor(c/3))%2===0;case 5:return ((r*c)%2+(r*c)%3)===0;
    case 6:return (((r*c)%2+(r*c)%3)%2)===0;case 7:return (((r*c)%3+(r+c)%2)%2)===0;
  }}
  function build(code,maskPattern,test){
    const n=21,M=Array.from({length:n},()=>Array(n).fill(null));
    function finder(row,col){for(let r=-1;r<=7;r++)for(let c=-1;c<=7;c++){const rr=row+r,cc=col+c;if(rr>=0&&rr<n&&cc>=0&&cc<n)M[rr][cc]=(r>=0&&r<=6&&(c===0||c===6)||c>=0&&c<=6&&(r===0||r===6)||r>=2&&r<=4&&c>=2&&c<=4)?true:false;}}
    finder(0,0);finder(n-7,0);finder(0,n-7);
    for(let i=8;i<n-8;i++)if(M[i][6]===null)M[i][6]=i%2===0;
    for(let j=8;j<n-8;j++)if(M[6][j]===null)M[6][j]=j%2===0;
    const bits=bchTypeInfo((1<<3)|maskPattern);
    for(let i=0;i<15;i++){
      const mod=!test&&((bits>>i)&1)===1;
      const r=i<6?i:i<8?i+1:n-15+i;
      if(M[r][8]===null)M[r][8]=mod;
      const c=i<8?n-i-1:i<9?15-i:15-i-1;
      if(M[8][c]===null)M[8][c]=mod;
    }
    M[n-8][8]=!test;
    const db=[];for(const b of code)addBits(db,b,8);
    let idx=0,row=n-1,inc=-1,col=n-1;
    while(col>0){if(col===6)col--;while(true){for(let c=0;c<2;c++){const cc=col-c;if(M[row][cc]===null){let dark=idx<db.length?db[idx]:0;if(mask(maskPattern,row,cc))dark^=1;M[row][cc]=!!dark;idx++;}}row+=inc;if(row<0||row>=n){row-=inc;inc=-inc;break;}}col-=2;}
    return M;
  }
  function penalty(M){
    const n=M.length;let p=0;
    for(let r=0;r<n;r++)for(let c=0;c<n;c++){let same=0;for(let dr=-1;dr<=1;dr++)for(let dc=-1;dc<=1;dc++)if(dr||dc){const rr=r+dr,cc=c+dc;if(rr>=0&&rr<n&&cc>=0&&cc<n&&M[rr][cc]===M[r][c])same++;}if(same>5)p+=3+same-5;}
    for(let r=0;r<n-1;r++)for(let c=0;c<n-1;c++){const z=M[r][c]+M[r+1][c]+M[r][c+1]+M[r+1][c+1];if(z===0||z===4)p+=3;}
    for(let r=0;r<n;r++)for(let c=0;c<n-6;c++)if(M[r][c]&&!M[r][c+1]&&M[r][c+2]&&M[r][c+3]&&M[r][c+4]&&!M[r][c+5]&&M[r][c+6])p+=40;
    for(let c=0;c<n;c++)for(let r=0;r<n-6;r++)if(M[r][c]&&!M[r+1][c]&&M[r+2][c]&&M[r+3][c]&&M[r+4][c]&&!M[r+5][c]&&M[r+6][c])p+=40;
    let dark=0;for(let r=0;r<n;r++)for(let c=0;c<n;c++)if(M[r][c])dark++;p+=Math.abs(100*dark/n/n-50)/5*10;return p;
  }
  let modules=null,raw='';
  return {
    addData:function(data){raw=String(data||'');},
    make:function(){const code=dataCodewords(raw);let best=null,min=Infinity;for(let m=0;m<8;m++){const z=build(code,m,true);const l=penalty(z);if(l<min){min=l;best=m;}}modules=build(code,best,false);},
    getModuleCount:function(){return 21;},
    isDark:function(r,c){return !!modules[r][c];},
    createSvgTag:function(opts){opts=opts||{};const cs=opts.cellSize||4,margin=opts.margin==null?4:opts.margin,n=21,size=n*cs+margin*2;let s='<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 '+size+' '+size+'" width="'+size+'" height="'+size+'" shape-rendering="crispEdges"><rect width="100%" height="100%" fill="white"/><path d="';for(let r=0;r<n;r++)for(let c=0;c<n;c++)if(modules[r][c])s+='M'+(c*cs+margin)+' '+(r*cs+margin)+'h'+cs+'v'+cs+'h-'+cs+'z';return s+'" fill="black"/></svg>';}
  };
}
