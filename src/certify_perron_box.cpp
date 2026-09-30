// Outward integer-interval scalar certificate; floating values are used only for elapsed-time diagnostics.
// Every proof quantity uses a 2^-56 integer enclosure; oversized products use exact GMP fallback.
#include <vector>
#include <gmpxx.h>
#include <array>
#include <cmath>
#include <iostream>
#include <algorithm>
#include <chrono>
#include <stdexcept>

using namespace std;using Int=__int128_t;using UInt=__uint128_t;
constexpr int BITS=56;const Int UNIT=Int(1)<<BITS;Int MAX_ENDPOINT=0;unsigned long long GMP_FALLBACKS=0;
string istr(Int x){if(!x)return "0";bool n=x<0;UInt a=n?UInt(-x):UInt(x);string s;while(a){s.push_back(char('0'+a%10));a/=10;}if(n)s+='-';reverse(s.begin(),s.end());return s;}
Int parsei(const string&s){bool n=s[0]=='-';Int x=0;for(size_t i=n;i<s.size();i++){if(x>((Int(1)<<120)-9)/10)throw runtime_error("integer input outside checked range");x=x*10+(s[i]-'0');}return n?-x:x;}
Int floordiv(Int a,Int b){if(b<=0)throw runtime_error("nonpositive divisor");Int q=a/b,r=a%b;return q-(r<0);}
Int ceildiv(Int a,Int b){if(b<=0)throw runtime_error("nonpositive divisor");Int q=a/b,r=a%b;return q+(r>0);}
Int productdiv(Int a,Int b,Int den,bool ceil){Int v;if(!__builtin_mul_overflow(a,b,&v))return ceil?ceildiv(v,den):floordiv(v,den);GMP_FALLBACKS++;mpz_class A(istr(a)),B(istr(b)),D(istr(den)),Q;mpz_class P=A*B;if(ceil)mpz_cdiv_q(Q.get_mpz_t(),P.get_mpz_t(),D.get_mpz_t());else mpz_fdiv_q(Q.get_mpz_t(),P.get_mpz_t(),D.get_mpz_t());return parsei(Q.get_str());}
struct Real{Int lo,hi;Real(long long n=0):lo(Int(n)*UNIT),hi(Int(n)*UNIT){MAX_ENDPOINT=max(MAX_ENDPOINT,max(-lo,hi));} Real(Int a,Int b):lo(a),hi(b){if(a>b)throw runtime_error("reversed interval");if(a<-(Int(1)<<120)||b>(Int(1)<<120))throw runtime_error("interval outside checked range");MAX_ENDPOINT=max(MAX_ENDPOINT,max(-a,b));}explicit operator bool()const{return lo||hi;}};
Real operator+(Real a,Real b){return {a.lo+b.lo,a.hi+b.hi};}Real operator-(Real a){return {-a.hi,-a.lo};}Real operator-(Real a,Real b){return a+-b;}
Real operator*(Real a,Real b){Int l=productdiv(a.lo,b.lo,UNIT,false),h=productdiv(a.lo,b.lo,UNIT,true);for(auto x:{a.lo,a.hi})for(auto y:{b.lo,b.hi}){l=min(l,productdiv(x,y,UNIT,false));h=max(h,productdiv(x,y,UNIT,true));}return {l,h};}
Real operator/(Real a,Real b){if(b.lo<=0)throw runtime_error("interval denominator not positive");Int l=productdiv(a.lo,UNIT,b.lo,false),h=productdiv(a.lo,UNIT,b.lo,true);for(auto x:{a.lo,a.hi})for(auto y:{b.lo,b.hi}){l=min(l,productdiv(x,UNIT,y,false));h=max(h,productdiv(x,UNIT,y,true));}return {l,h};}
Real&operator+=(Real&a,Real b){a=a+b;return a;}Real&operator*=(Real&a,Real b){a=a*b;return a;}
Real absI(Real a){if(a.lo>=0)return a;if(a.hi<=0)return -a;return {0,max(-a.lo,a.hi)};}
Real ipow(Real a,int n){if(n<0)return Real(1)/ipow(a,-n);Real v=1;while(n){if(n&1)v*=a;n>>=1;if(n)a*=a;}return v;}
Real rational(Int n,Int d){return {productdiv(n,UNIT,d,false),productdiv(n,UNIT,d,true)};}

struct Node{vector<pair<int,int>>adj;int lo=1,hi=3;};
struct Component{vector<int>seq;vector<int>edge;bool cycle;};
struct Graph{int p;vector<Node>v;vector<Component>cs;};
Real z,w,lam,mu,rho,kv,kq,pv[5],qv[5],zw[5],T;
Graph graph(int m,int r,int p){
 Graph g;g.p=p;g.v.resize(m);for(int i=1;i<m;i++)g.v[i].hi=i<r?4:3;
 for(int target:{r,p})for(int i=1;i<m;i++){
  int j=(target-i+m)%m;if(j==0||j<i||i==r||i==p||j==r||j==p)continue;int th=(i+j<m?4:3);
  if(i==j)g.v[i].lo=2;else{g.v[i].adj.push_back({j,th});g.v[j].adj.push_back({i,th});}
 }
 vector<bool>seen(m);seen[r]=seen[p]=true;
 for(int root=1;root<m;root++)if(!seen[root]){
  vector<int>vs,st{root};seen[root]=true;
  while(!st.empty()){int v=st.back();st.pop_back();vs.push_back(v);for(auto e:g.v[v].adj)if(!seen[e.first]){seen[e.first]=true;st.push_back(e.first);}}
  int head=*min_element(vs.begin(),vs.end());bool cyc=true;for(int v:vs)if(g.v[v].adj.size()<2){head=v;cyc=false;break;}
  vector<int>seq{head},ed;int prev=-1,cur=head;
  while(true){int next=-1,b=0;for(auto e:g.v[cur].adj)if(e.first!=prev){next=e.first;b=e.second;break;}if(next<0)break;ed.push_back(b);if(next==head)break;seq.push_back(next);prev=cur;cur=next;}
  if(cyc){int h=-1;for(int i=0;i<(int)seq.size();i++)if(ed[i]==4&&ed[(i+seq.size()-1)%seq.size()]==3){h=i;break;}if(h<0)throw runtime_error("unmixed cycle");rotate(seq.begin(),seq.begin()+h,seq.end());rotate(ed.begin(),ed.begin()+h,ed.end());}
  if(seq.size()!=vs.size())throw runtime_error("badpath");g.cs.push_back({seq,ed,cyc});
 }
 return g;
}
Real partition(const Graph&g,int mode){
 Real out=zw[4]*zw[4];
 for(auto&comp:g.cs){
  auto&seq=comp.seq;auto&ed=comp.edge;int head=seq[0];Real val=0;
  for(int first=g.v[head].lo;first<=g.v[head].hi;first++){
   array<Real,5>state{},next{};state[first]=comp.cycle?1:zw[first];
   for(int pos=0;pos<(int)ed.size();){
    int n=1;if(mode&&ed[pos]==3)while(pos+n<(int)ed.size()&&ed[pos+n]==3)n++;
    int end=seq[(pos+n)%seq.size()];next.fill(0);
    for(int a=1;a<=4;a++)if(state[a])for(int b=g.v[end].lo;b<=g.v[end].hi;b++){
     Real factor=0;
     if(!mode||ed[pos]==4){if(a+b>=ed[pos])factor=zw[b];}
     else if(a<=3&&b<=3){factor=ipow(w*lam,n)*ipow(z,b)*pv[a]*pv[b]/kv;if(mode==2)factor+=ipow(absI(w*mu),n)*ipow(z,b)*qv[a]*qv[b]/kq;}
     next[b]+=state[a]*factor;
    }
    state=next;pos+=n;
   }
   if(comp.cycle)val+=state[first];else for(int a=1;a<=4;a++)val+=state[a];
  }
  out*=val;
 }
 return out;
}

using Mat=array<array<Real,4>,4>;using Row=array<Real,4>;
Mat identity(){Mat a{};for(int i=0;i<4;i++)a[i][i]=1;return a;}
Mat product(const Mat&a,const Mat&b){Mat c{};for(int i=0;i<4;i++)for(int k=0;k<4;k++)if(a[i][k])for(int j=0;j<4;j++)c[i][j]+=a[i][k]*b[k][j];return c;}
Row rowmul(const Row&a,const Mat&b){Row c{};for(int i=0;i<4;i++)for(int j=0;j<4;j++)c[j]+=a[i]*b[i][j];return c;}
Real dotrow(const Row&a,const Row&b){Real s=0;for(int i=0;i<4;i++)s+=a[i]*b[i];return s;}

vector<Mat>Dpowers;
Mat strong(const Graph&g,const Component&c,int from,int to){int k=to-from;Mat a=Dpowers[k];if(k){int end=c.seq[to%c.seq.size()];for(int j=1;j<=4;j++)if(j<g.v[end].lo||j>g.v[end].hi)for(int i=0;i<4;i++)a[i][j-1]=0;}return a;}
Real partition_basis(const Graph&g,int mode){
 array<Row,2> right{},left{};for(int a=1;a<=3;a++){right[0][a-1]=pv[a];right[1][a-1]=Real(a==1?1:-1)*qv[a];left[0][a-1]=ipow(z,a)*right[0][a-1]/kv;left[1][a-1]=ipow(z,a)*right[1][a-1]/kq;}
 auto absif=[&](Real x){return mode==2?absI(x):x;};auto powmode=[&](int k,int n){return ipow(w*(k==0?lam:(mode==3?mu:absI(mu))),n);};
 Real out=zw[4]*zw[4];
 for(auto&c:g.cs){
  struct Carry{int start,n,end;};vector<Carry>runs;
  for(int i=0;i<(int)c.edge.size();){if(c.edge[i]==4){i++;continue;}int n=1;while(i+n<(int)c.edge.size()&&c.edge[i+n]==3)n++;runs.push_back({i,n,c.seq[(i+n)%c.seq.size()]});i+=n;}
  bool corner=c.edge.empty()&&c.seq[0]>g.p;
  if(corner)runs.push_back({0,0,c.seq[0]});
  if(runs.empty()){
   Real val=0;for(int first=g.v[c.seq[0]].lo;first<=g.v[c.seq[0]].hi;first++){Row a{};a[first-1]=zw[first];a=rowmul(a,strong(g,c,0,c.edge.size()));for(Real v:a)val+=v;}out*=val;continue;
  }
  vector<array<Row,2>>ends;
  for(auto run:runs){auto f=left;for(int k=0;k<2;k++)for(int a=1;a<=4;a++)if(a<g.v[run.end].lo||a>g.v[run.end].hi)f[k][a-1]=0;ends.push_back(f);}
  Mat prefix=strong(g,c,0,runs[0].start),suffix=strong(g,c,runs.back().start+runs.back().n,c.edge.size());
  vector<array<array<Real,2>,2>>between;
  for(size_t j=1;j<runs.size();j++){Mat d=strong(g,c,runs[j-1].start+runs[j-1].n,runs[j].start);array<array<Real,2>,2>b{};for(int k=0;k<2;k++)for(int l=0;l<2;l++)b[k][l]=absif(dotrow(rowmul(ends[j-1][k],d),right[l]));between.push_back(b);}
  Real val=0;int states=mode==1?1:2;
  if(!c.cycle){
   Row h{};for(int a=corner?1:g.v[c.seq[0]].lo;a<=(corner?3:g.v[c.seq[0]].hi);a++)h[a-1]=zw[a];h=rowmul(h,prefix);array<Real,2>st{};
   for(int k=0;k<states;k++)st[k]=absif(dotrow(h,right[k]))*powmode(k,runs[0].n);
   for(size_t j=1;j<runs.size();j++){array<Real,2>next{};for(int k=0;k<states;k++)for(int l=0;l<states;l++)next[l]+=st[k]*between[j-1][k][l]*powmode(l,runs[j].n);st=next;}
   Row ones={1,1,1,1};for(int k=0;k<states;k++)val+=st[k]*absif(dotrow(rowmul(ends.back()[k],suffix),ones));
  }else{
   Mat wrap=product(suffix,prefix);
   for(int first=0;first<states;first++){
    array<Real,2>st{};st[first]=powmode(first,runs[0].n);
    for(size_t j=1;j<runs.size();j++){array<Real,2>next{};for(int k=0;k<states;k++)for(int l=0;l<states;l++)next[l]+=st[k]*between[j-1][k][l]*powmode(l,runs[j].n);st=next;}
    for(int last=0;last<states;last++)val+=st[last]*absif(dotrow(rowmul(ends.back()[last],wrap),right[first]));
   }
  }
  out*=val;
 }
 return out;
}

int main(int argc,char**argv){
 if(argc<10)throw runtime_error("P znum zden wunit lamlo lamhi Tlo Thi pureflag required");int P=atoi(argv[1]);z=rational(parsei(argv[2]),parsei(argv[3]));w=Real(parsei(argv[4]),parsei(argv[4]));lam=Real(parsei(argv[5]),parsei(argv[6]));T=Real(parsei(argv[7]),parsei(argv[8]));bool pureonly=atoi(argv[9]);
 Real b=z*z+z*z*z;mu=b-lam;rho=-mu/lam;
 for(int a=1;a<=4;a++){zw[a]=w*ipow(z,a);pv[a]=a==1?b/lam:Real(1);qv[a]=a==1?lam/z:Real(1);}kv=z*pv[1]*pv[1]+b;kq=z*qv[1]*qv[1]+b;
 Mat D{};for(int a=1;a<=4;a++)for(int b=1;b<=4;b++)if(a+b>=4)D[a-1][b-1]=zw[b];Dpowers.push_back(identity());for(int k=1;k<=P+2;k++)Dpowers.push_back(product(Dpowers.back(),D));
 Real pure=0,mixed=0,shortsum=0;auto start=chrono::steady_clock::now();long long graphs=0;
 for(int p=2;p<=P;p++){
  Real rowshort=0,rowpure=0,rowmixed=0;
  for(int r=1;r<p;r++){
   int d=p-r,m0=2*p+1;Real fixed=ipow(T,d/3+1)*ipow(w,-2*p);
   if(!pureonly)for(int m=p+1;m<m0;m++){auto g=graph(m,r,p);graphs++;rowshort+=ipow(w,-(m-1))*partition(g,0);}
   for(int j=0;j<(pureonly?2:2*d);j++){
    int m=m0+j;auto g=graph(m,r,p);graphs++;Real pr=partition_basis(g,1),pre=fixed*ipow(w,-((m-1)%2));
    if(j<2)rowpure+=pre*pr/(Real(1)-w*w*lam*lam);
    if(!pureonly){Real ab=partition_basis(g,2),diff=ab-pr;if(diff.hi<0)throw runtime_error("abs below pure");diff.lo=max(Int(0),diff.lo);rowmixed+=pre*diff/(Real(1)-ipow(w*lam,2*d)*rho*rho);}
   }
  }
  shortsum+=rowshort;pure+=rowpure;mixed+=rowmixed;
  if(p%10==0)cerr<<"p="<<p<<" sec="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
 }
 cout<<"{\"P\":"<<P<<",\"scale\":"<<istr(UNIT)<<",\"z_num\":"<<argv[2]<<",\"z_den\":"<<argv[3]<<",\"w_units\":"<<argv[4]<<",\"lambda_lo_units\":"<<argv[5]<<",\"lambda_hi_units\":"<<argv[6]<<",\"T_lo_units\":"<<argv[7]<<",\"T_hi_units\":"<<argv[8]<<",\"pure_only\":"<<(pureonly?"true":"false")<<",\"graphs\":"<<graphs<<",\"short_hi_units\":"<<istr(shortsum.hi)<<",\"pure_hi_units\":"<<istr(pure.hi)<<",\"mixed_hi_units\":"<<istr(mixed.hi)<<",\"max_observed_endpoint_units\":"<<istr(MAX_ENDPOINT)<<",\"GMP_product_fallback_count\":"<<GMP_FALLBACKS<<"}\n";
 return 0;
}
