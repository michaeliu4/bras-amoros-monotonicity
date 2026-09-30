// Exact graph-relaxation coefficients, never a numerical-semigroup census.
// Counts cap4 words by their unique two rightmost 4s, retaining all inequalities
// targeting these pivots. Arbitrary-precision integers throughout.
#include <gmpxx.h>
#include <vector>
#include <array>
#include <iostream>
#include <fstream>
#include <algorithm>
#include <chrono>
#include <cstdio>
#ifndef CAP
#define CAP 4
#endif
static_assert(CAP==4 || CAP==5, "CAP must be4 or5");
using namespace std; using cpp_int=mpz_class;
using Poly=vector<cpp_int>;
struct Comp {vector<int>v; bool cycle;};
struct Graph {int m,r,p; vector<vector<pair<int,int>>> adj; vector<int> lo,hi;vector<Comp> comps;};
Graph graph(int m,int r,int p) {
 Graph G{m,r,p,vector<vector<pair<int,int>>>(m),vector<int>(m,1),vector<int>(m)};
 for(int i=1;i<m;i++)G.hi[i]=(i<r?CAP:CAP-1);
 G.hi[r]=G.hi[p]=0;
 for(int t:{r,p})for(int i=1;i<m;i++)for(int s:{t,m+t}){
  int j=s-i;if(j<i||j>=m||j<=0||i==r||i==p||j==r||j==p)continue;
  int bound=(s<m?CAP:CAP-1);
  if(i==j)G.lo[i]=max(G.lo[i],(bound+1)/2);
  else{G.adj[i].push_back({j,bound});G.adj[j].push_back({i,bound});}
 }
 vector<bool> seen(m);
 for(int i=1;i<m;i++)if(i!=r&&i!=p&&!seen[i]){
  vector<int> verts,stack{i};seen[i]=true;
  while(!stack.empty()){int v=stack.back();stack.pop_back();verts.push_back(v);for(auto [w,b]:G.adj[v])if(!seen[w]){seen[w]=true;stack.push_back(w);}}
  int head=*min_element(verts.begin(),verts.end());bool cycle=true;
  for(int v:verts)if(G.adj[v].size()<2){head=v;cycle=false;break;}
  vector<int> seq{head};int prev=-1,cur=head;
  while(true){int next=-1;for(auto [w,b]:G.adj[cur])if(w!=prev&&w!=head){next=w;break;}if(next<0)break;seq.push_back(next);prev=cur;cur=next;}
  if(seq.size()!=verts.size())throw runtime_error("bad component");
  G.comps.push_back({seq,cycle});
 }
 return G;
}
int bound(const Graph&G,int v,int w){for(auto[j,b]:G.adj[v])if(j==w)return b;throw runtime_error("missing edge");}
vector<int> domain(const Graph&G,int v,int mode){vector<int>d;for(int x=G.lo[v];x<=G.hi[v];x++){
 if(mode==1&&x==1)continue;
 if(mode==2&&((x==1)!=(v==G.m-1)))continue;
 d.push_back(x);
}return d;}
int minimum(const Graph&G,int mode){int sum=0;
 for(auto &c:G.comps){int val=100000;int head=c.v[0];
  for(int first:domain(G,head,mode)){
   array<int,CAP+1> st;st.fill(100000);st[first]=first;
   for(int j=1;j<(int)c.v.size();j++){
    array<int,CAP+1> ns;ns.fill(100000);int b=bound(G,c.v[j-1],c.v[j]);
    for(int x:domain(G,c.v[j],mode))for(int y=1;y<=CAP;y++)if(x+y>=b)ns[x]=min(ns[x],st[y]+x);st=ns;
   }
   for(int last=1;last<=CAP;last++)if(!c.cycle||last+first>=bound(G,c.v.back(),head))val=min(val,st[last]);
  }sum+=val;
 }return sum;}


const int INF=100000000;
int component_minimum(const Graph&G,const Comp&c){
 int answer=INF;int head=c.v[0];
 vector<int> starts=c.cycle?domain(G,head,0):vector<int>{0};
 for(int fixed:starts){
  array<int,CAP+1> st;st.fill(INF);
  for(int x:domain(G,head,0))if(!c.cycle||x==fixed)st[x]=x;
  for(int j=1;j<(int)c.v.size();j++){
   array<int,CAP+1> ns;ns.fill(INF);int b=bound(G,c.v[j-1],c.v[j]);
   for(int x:domain(G,c.v[j],0))for(int y=1;y<=CAP;y++)if(x+y>=b)ns[x]=min(ns[x],st[y]+x);st=ns;
  }
  for(int x=1;x<=CAP;x++)if(!c.cycle||x+fixed>=bound(G,c.v.back(),head))answer=min(answer,st[x]);
 }
 return answer;
}
// Return z^(-minimum) times the exact component polynomial, truncated at
// excess degree slack. Digits have width N+2, so all operations are carry-free.
cpp_int packed_component(const Graph&G,const Comp&c,int mincost,int slack,int width){
 int n=c.v.size(),budget=mincost+slack,head=c.v[0];cpp_int total=0;
 vector<int> starts=c.cycle?domain(G,head,0):vector<int>{0};
 vector<vector<int>> dom(n);vector<int> edge(n);
 for(int j=0;j<n;j++){dom[j]=domain(G,c.v[j],0);if(j)edge[j]=bound(G,c.v[j-1],c.v[j]);}
 for(int fixed:starts){
  vector<array<int,CAP+1>> future(n);for(auto&a:future)a.fill(INF);
  for(int x:dom[n-1])if(!c.cycle||x+fixed>=bound(G,c.v.back(),head))future[n-1][x]=0;
  for(int j=n-2;j>=0;j--)for(int x:dom[j])for(int y:dom[j+1])if(x+y>=edge[j+1])future[j][x]=min(future[j][x],y+future[j+1][y]);
  array<int,CAP+1> low;low.fill(INF);int offset=INF;
  for(int x:dom[0])if((!c.cycle||x==fixed)&&x+future[0][x]<=budget){low[x]=x;offset=min(offset,x);}
  if(offset==INF)continue;
  array<cpp_int,CAP+1> st,ns;
  for(int x:dom[0])if(low[x]<INF)mpz_setbit(st[x].get_mpz_t(),width*(x-offset));
  for(int j=1;j<n;j++){
   array<int,CAP+1> nextlow;nextlow.fill(INF);int newoffset=INF;
   for(int x:dom[j]){
    for(int y=1;y<=CAP;y++)if(x+y>=edge[j])nextlow[x]=min(nextlow[x],low[y]+x);
    if(nextlow[x]+future[j][x]>budget)nextlow[x]=INF;
    newoffset=min(newoffset,nextlow[x]);
   }
   if(newoffset==INF){for(auto&a:st)a=0;break;}
   array<cpp_int,CAP+2> suffix;
   for(int y=CAP;y>=1;y--)suffix[y]=suffix[y+1]+st[y];
   for(auto&a:ns)a=0;
   for(int x:dom[j])if(nextlow[x]<INF){
    const auto &sum=suffix[max(1,edge[j]-x)];int delta=offset+x-newoffset;
    if(delta>=0)mpz_mul_2exp(ns[x].get_mpz_t(),sum.get_mpz_t(),width*delta);
    else{
     if(!mpz_divisible_2exp_p(sum.get_mpz_t(),width*(-delta)))throw runtime_error("nonexact degree normalization");
     mpz_fdiv_q_2exp(ns[x].get_mpz_t(),sum.get_mpz_t(),width*(-delta));
    }
    int max_exponent=budget-newoffset-future[j][x];
    if(max_exponent<0)throw runtime_error("bad suffix budget");
    mpz_fdiv_r_2exp(ns[x].get_mpz_t(),ns[x].get_mpz_t(),width*(max_exponent+1));
   }
   st.swap(ns);low=nextlow;offset=newoffset;
  }
  cpp_int sum=0;for(int x=1;x<=CAP;x++)sum+=st[x];
  if(sum!=0){if(offset<mincost)throw runtime_error("bad component normalization");mpz_mul_2exp(sum.get_mpz_t(),sum.get_mpz_t(),width*(offset-mincost));total+=sum;}
 }
 mpz_fdiv_r_2exp(total.get_mpz_t(),total.get_mpz_t(),width*(slack+1));return total;
}
int main(int argc,char**argv){
 int N=argc>1?stoi(argv[1]):60;if(N<2*CAP || N>2000){cerr<<"Cutoff must lie between2*CAP and2000\n";return 2;}
 string path=argc>2?argv[2]:"offset_q4.json";int width=N+2,budget=N-2*CAP;
 vector<cpp_int>buckets(budget+1);int mlo=argc>3?stoi(argv[3]):3;int mhi=argc>4?stoi(argv[4]):N-2*CAP+3;
 if(mlo<3 || mhi>N-2*CAP+3 || mlo>mhi)throw runtime_error("invalid multiplicity shard");
 int pmax=argc>5?stoi(argv[5]):N;int pmin=argc>6?stoi(argv[6]):2;
 if(pmin<2 || pmax>N || pmin>pmax)throw runtime_error("invalid pivot shard");
 long graphs=0,nonzero=0;auto start=chrono::steady_clock::now();
 for(int m=mlo;m<=mhi;m++){
  for(int p=pmin;p<m && p<=pmax;p++)for(int r=1;r<p;r++){
   graphs++;if((CAP-1)*m+p+1>2*N)continue;
   auto G=graph(m,r,p);vector<int> mins;int minimum=0;
   for(auto&c:G.comps){int cost=component_minimum(G,c);mins.push_back(cost);minimum+=cost;}
   if(minimum>budget)continue;nonzero++;int slack=budget-minimum;cpp_int out=1;
   for(int k=0;k<(int)G.comps.size();k++){out*=packed_component(G,G.comps[k],mins[k],slack,width);mpz_fdiv_r_2exp(out.get_mpz_t(),out.get_mpz_t(),width*(slack+1));}
   buckets[minimum]+=out;
  }
  if(m%10==0)cerr<<"m="<<m<<" graphs="<<graphs<<" nonzero="<<nonzero<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
 }
 cpp_int accumulator=0;
 for(int g=0;g<=budget;g++){mpz_mul_2exp(buckets[g].get_mpz_t(),buckets[g].get_mpz_t(),width*g);accumulator+=buckets[g];}
 vector<cpp_int>A(N+1);for(int i=0;i<=budget;i++){mpz_fdiv_r_2exp(A[i+2*CAP].get_mpz_t(),accumulator.get_mpz_t(),width);mpz_fdiv_q_2exp(accumulator.get_mpz_t(),accumulator.get_mpz_t(),width);}
 if(accumulator!=0)throw runtime_error("unexpected high-degree output");
 double seconds=chrono::duration<double>(chrono::steady_clock::now()-start).count();
 const string temporary=path+".tmp";
 ofstream out(temporary, ios::out|ios::trunc);
 if(!out)throw runtime_error("cannot open temporary output: "+temporary);
 out<<"{\"scope\":\"Exact cap-four or cap-five two-rightmost-pivot relaxation via normalized carry-free Kronecker encoding and suffix-cost pruning; not a semigroup census\",\"N\":"<<N<<",\"cap\":"<<CAP<<",\"mlo\":"<<mlo<<",\"mhi\":"<<mhi<<",\"pmin\":"<<pmin<<",\"pmax\":"<<pmax<<",\"width\":"<<width<<",\"graphs\":"<<graphs<<",\"nonzero\":"<<nonzero<<",\"seconds\":"<<seconds<<",\"all\":[";
 for(int i=0;i<=N;i++){if(i)out<<",";out<<A[i];}out<<"]}\n";
 out.flush();if(!out)throw runtime_error("output write failed: "+temporary);
 out.close();if(!out)throw runtime_error("output close failed: "+temporary);
 if(std::rename(temporary.c_str(),path.c_str())!=0)throw runtime_error("atomic output rename failed: "+path);
 cerr<<"finished seconds="<<seconds<<"\n";
}
