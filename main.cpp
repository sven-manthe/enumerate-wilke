#include<bits/stdc++.h>
using std::string;
using std::vector;
using std::pair;
using std::optional;
using std::ostream;

using std::cout;
using std::cerr;
using std::endl;

template<typename T>
ostream& operator<< (ostream& out, const vector<T>& v) {
    out << "[";
    size_t last = v.size() - 1;
    for(size_t i = 0; i < v.size(); ++i) {
        out << v[i];
        if (i != last) 
            out << ", ";
    }
    out << "]";
    return out;
}

//iterate all tuples of size exp in r
template<typename T, typename Iter=vector<T>::const_iterator, typename Ran=vector<T>>
struct comb_ran {
  Ran r;
  int exp;
  bool injections_only;
  
  struct iter {
    const Ran&r;
    bool injections_only;
    vector<Iter>v;
    bool eq_begin=true;
    bool injective()const {
      if(!injections_only)return true;
      for(auto i:v){
	int cnt=0;
	for(auto j:v)cnt+=(i==j);
	if(cnt>1)return false;
      }
      return true;
    }
    void step() {
      for(int i=v.size()-1;;--i){
	++v[i];
	if(i>0&&v[i]==r.end())v[i]=r.begin();
	else return;
      }
    }
    iter&operator++() {
      if(v.size()==0)
	eq_begin=false;
      else
	while(v[0]!=r.end()){
	  step();
	  if(injective())break;
	}
      return *this;
    }
    auto operator<=>(const iter&i)const {
      return pair(v,eq_begin) <=> pair(i.v,i.eq_begin);
    }
    auto operator==(const iter&i)const {
      return v == i.v && eq_begin == i.eq_begin;
    }
    vector<T>operator*()const {
      vector<T>w;
      for(Iter i:v)w.push_back(*i);
      return w;
    }
  };

  iter begin()const {
    vector<Iter>v;
    for(int i=0;i<exp;++i)v.emplace_back(r.begin());
    iter i={r,injections_only,v,true};
    if(exp>0)
      while(i.v[0]!=r.end()&&!i.injective())i.step();
    return i;
  }
  iter end()const {
    vector<Iter>v;
    for(int i=0;i<exp;++i)v.emplace_back(r.begin());
    iter i={r,injections_only,v,exp>0};
    if(exp>0)i.v[0]=r.end();
    return i;
  }
};

struct V {
  uint8_t val;
  bool operator==(const V&x)const = default;
  V&operator++() {
    ++val; return *this;
  }
};
ostream& operator<< (ostream& out, V v) {
  return out << char('p'+v.val);
}
struct H {
  uint8_t val;
  bool operator==(const H&x)const = default;
  H&operator++() {
    ++val; return *this;
  }
};
ostream& operator<< (ostream& out, H h) {
  return out << char('a'+h.val);
}


template<typename S, typename T>struct map {
  vector<T>table;

  T&operator()(S s) {
    return table[s.val];
  }
  T operator()(S s)const {
    return table[s.val];
  }
};
template<typename T>map<T,T>id_map(int size){
  vector<T>table(size);
  for(uint8_t i=0;i<size;++i)table[i]=T{i};
  return {table};
}


template<typename T>struct subset {
  int amb_size;
  unsigned val;
  subset&operator++() {
    ++val; return *this;
  }
  auto operator<=>(const subset&i)const = default;
  struct bit_ref {
    unsigned*val;
    int i;
    operator bool()const {
      return *val&(1u<<i);
    }
    bit_ref&operator=(bool b) {
      if(b)*val=*val|(1u<<i);
      else *val=*val&~(1u<<i);
      return *this;
    }
    bit_ref&operator=(const bit_ref&b) {
      return *this = bool(b);
    }
  };
  bit_ref operator[](T i) {
    return {&val,i.val};
  }
  bool operator[](T i)const {
    return val&(1u<<i.val);
  }
  static subset empty(int size) {
    return {size,0};
  }
  static subset full(int size) {
    return {size,(1u<<size)-1};
  }
  static subset singleton(int size, T i) {
    return {size,1u<<i.val};
  }
  subset unio(subset s)const {
    return {amb_size,val|s.val};
  }
  subset inter(subset s)const {
    return {amb_size,val&s.val};
  }
  subset diff(subset s)const {
    return {amb_size,val&~s.val};
  }
  subset comp()const {
    return full(amb_size).diff(*this);
  }
  bool is_sub(subset s)const {
    return diff(s)==empty(amb_size);
  }
  template<typename P>static subset build(int size, P f){
    auto s=empty(size);
    for(T j={0};j.val<size;++j)
      s[j]=f(j);
    return s;
  }

  //maps the i-th element of a subset to i
  map<T,T>inverse()const {
    map<T,T>f{vector<T>(amb_size)};
    T i={0};
    for(T j={0};j.val<amb_size;++j)
      if((*this)[j]){
	f(j)=i;
	++i;
      }
      else f(j)=T{uint8_t(-1)};
    return f;
  }
  struct iter;
  iter begin()const;
  iter end()const;
  T min()const;
  T max()const;
  int card()const;
};
template<typename T>struct subset<T>::iter {
  subset s;
  T i;
  void move(){
    while(i.val<s.amb_size&&!s[i])++i;
  }
  iter&operator++() {
    ++i; move(); return *this;
  }
  auto operator<=>(const iter&i)const = default;
  T operator*()const {
    return i;
  }
};
template<typename T>subset<T>::iter subset<T>::begin()const {
  iter i={*this,0};
  i.move();
  return i;
}
template<typename T>subset<T>::iter subset<T>::end()const {
  return {*this,uint8_t(amb_size)};
}
template<typename T>int subset<T>::card()const {
  int x=0;
  for(T _: *this)++x;
  return x;
}
template<typename T>T subset<T>::min()const {
  return *begin();
}
template<typename T>T subset<T>::max()const {
  T x{uint8_t(-1)};
  for(auto y: *this)x=y;
  return x;
}
template<typename T>ostream& operator<< (ostream& out, subset<T> s) {
  for(uint8_t i=0;i<s.amb_size;++i) out<<s[T{i}];
  return out;
}


struct generating_set;
struct semigroup {
  int size;
  vector<V>table;
  auto operator<=>(const semigroup&s)const = default;

  semigroup(vector<V>table): size(0), table(table) {
    while(size*size<table.size())++size;
  }

  V mul(V x, V y)const {
    return table[x.val*size+y.val];
  }
  V mul(const vector<V>&X)const {
    V x=X[0];
    for(int i=1;i<X.size();++i)
      x=mul(x,X[i]);
    return x;
  }
  V idem_pow(V x)const {
    V y=x;
    while(y!=mul(y,y))y=mul(y,x);
    return y;
  }

  bool infix(V x, V y)const {
    for(V a={0};a.val<size;++a)
      for(V b={0};b.val<size;++b)
	if(y==mul(mul(a,x),b))return true;
    return false;
  }
  bool infix_eq(V x, V y)const {
    return infix(x,y) && infix(y,x);
  }
  
  auto idempotents()const {
    return subset<V>::build(size, [&](V x){return x==mul(x,x);});
  }
  auto left_absorbing()const {
    return subset<V>::build(size, [&](V x){
      for(V y={0};y.val<size;++y)if(mul(x,y)!=x)return false;
      return true;
    });
  }
  auto left_units()const {
    return subset<V>::build(size, [&](V x){
      for(V y={0};y.val<size;++y)if(mul(x,y)!=y)return false;
      return true;
    });
  }
  auto mul(subset<V> X, subset<V> Y)const {
    auto s = subset<V>::empty(size);
    for(auto x:X)for(auto y:Y)s[mul(x,y)]=1;
    return s;
  }
  auto saturate(subset<V> X)const {
    auto A=X;
    while(true){
      A=mul(X,A).diff(X);
      if(A==subset<V>::empty(size))return X;
      X=X.unio(A);
    }
  }
  
  bool subsemigroup(subset<V> X)const {
    return saturate(X)==X;
  }
  bool generates(subset<V> X)const {
    return saturate(X)==subset<V>::full(size);
  }
  auto min_gen()const {
    auto G = subset<V>::full(size);
    for(subset X=subset<V>::empty(size);X<subset<V>::full(size);++X)
      if(generates(X)&&X.card()<G.card())G=X;
    return G;
  }

  semigroup opposite()const {
    auto S=*this;
    for(uint8_t i=0;i<size;++i)
      for(uint8_t j=0;j<size;++j)
	S.table[i*size+j]=mul(V{j},V{i});
    return S;
  }
  generating_set min_gen_set()const;
  static const semigroup empty;
};
const semigroup semigroup::empty{{}};
semigroup read_table(string s){
  vector<V>t;
  for(char c:s)t.push_back(V{uint8_t(c-'1')});
  return t;
}

struct linked_pair {
  V s;
  V e;
  const semigroup&S;
  bool valid()const {
    return S.mul(s,e)==s && S.mul(e,e)==e;
  }
  bool conj(const linked_pair&l)const {
    for(V x={0}; x.val<S.size; ++x)
      for(V y={0}; y.val<S.size; ++y)
	if(S.mul(x,y)==e && S.mul(y,x)==l.e && l.s==S.mul(s,x))return true;
    return false;
  }
};
auto conj_classes(const semigroup&S) {
  vector<linked_pair>c;
  for(V s={0}; s.val<S.size; ++s)
    for(V e={0}; e.val<S.size; ++e){
      linked_pair l={s,e,S};
      if(!l.valid())goto skip;
      for(auto l2:c)if(l.conj(l2))goto skip;
      c.push_back(l);
    skip:;
    }
  return c;
}

struct generating_set : semigroup {
  subset<V> as_set;
  vector<vector<V>> reps; //represents each term as word of generators, using least possible prefix of generating set

  vector<V>&rep(V x) {
    return reps[x.val];
  }
  const vector<V>&rep(V x)const {
    return reps[x.val];
  }
  
  generating_set(semigroup s, subset<V>gens): semigroup(s), as_set(gens) {
    reps.resize(size);
    auto done=subset<V>::empty(size);
    for(auto i:as_set){
      rep(i).push_back(i);
      vector<V>add;
      add.push_back(i);
      done[i]=1;
      while(add.size()>0){
	vector<V> addn;
	for(V x: done)
	  for(V y:add){
	    if(!done[mul(x,y)]){
	      rep(mul(x,y))=rep(x);
	      for(V z:rep(y))rep(mul(x,y)).push_back(z);
	      addn.push_back(mul(x,y));
	      done[mul(x,y)]=1;
	    }
	    if(!done[mul(y,x)]){
	      rep(mul(y,x))=rep(y);
	      for(V z:rep(x))rep(mul(y,x)).push_back(z);
	      addn.push_back(mul(y,x));
	      done[mul(y,x)]=1;
	    }
	  }
	add=addn;
      }
    }
  }
  static const generating_set empty;
};
const generating_set generating_set::empty = {semigroup::empty, subset<V>::empty(0)};
generating_set semigroup::min_gen_set()const {
  return {*this, min_gen()};
}
struct sub_generating_set : generating_set {
  int num_gens; //use subsemigroup of dom generated by first num_gens generators
  subset<V> mem_set;

  sub_generating_set(generating_set S, int drop_gens):
    generating_set(S), num_gens(as_set.card()-drop_gens), mem_set(subset<V>::full(size)) {
    auto inv=as_set.inverse();
    for(V x={0};x.val<size;++x)
      for(V y:rep(x))
	if(inv(y).val>=num_gens)
	  mem_set[x]=0;
  }
  
  static const sub_generating_set empty;
};
const sub_generating_set sub_generating_set::empty = {generating_set::empty, 0};

struct partial_iso {
  sub_generating_set dom;
  semigroup codom;
  vector<V>table; //full table

  partial_iso(sub_generating_set dom, semigroup codom, const vector<V>&gen_table):
    dom(dom), codom(codom), table(dom.size) {
    int gi=0;
    for(auto it=dom.as_set.begin();gi<dom.num_gens;++gi,++it)
      table[(*it).val]=gen_table[gi];
    for(V i={0};i.val<dom.size;++i)
      if(dom.mem_set[i]){
	auto w=dom.rep(i);
	for(V&v:w)v=eval(v);
	table[i.val]=codom.mul(w);
      }
  }

  V eval(V x)const{
    return table[x.val];
  }
  
  bool surjective()const {
    vector<char>hit(codom.size);
    for(V i={0};i.val<dom.size;++i)
      if(dom.mem_set[i])
	hit[eval(i).val]=1;
    for(char c:hit)if(!c)return false;
    return true;
  }
  bool morphism()const {
    for(V x={0};x.val<dom.size;++x)
      for(V y={0};y.val<dom.size;++y)
	if(dom.mem_set[x]&&dom.mem_set[y]
	   &&codom.mul(eval(x),eval(y))!=eval(dom.mul(x,y)))return false;
    return true;
  }
  static const partial_iso empty;
};
const partial_iso partial_iso::empty = {sub_generating_set::empty, semigroup::empty, {}};

optional<partial_iso> find_iso(const sub_generating_set&dom,const semigroup&codom) {
  if(dom.mem_set.card()!=codom.size) return std::nullopt;
  if(dom.idempotents().inter(dom.mem_set).card()!=codom.idempotents().card())
    return std::nullopt;
  for(auto table: comb_ran<V>(id_map<V>(codom.size).table, dom.num_gens, true)){
    partial_iso i={dom,codom,table};
    if(i.surjective()&&i.morphism())
      return i;
  }
  return std::nullopt;
}
bool isomorphic(const semigroup&S, const semigroup&T){
  auto Sm=S.min_gen_set();
  sub_generating_set SG{Sm, 0};
  return find_iso(SG,T).has_value();
}
auto automorphisms(const semigroup&S) {
  vector<map<V,V>>res;
  auto Sm=S.min_gen_set();
  sub_generating_set SG{Sm, 0};
  for(auto table: comb_ran<V>(id_map<V>(S.size).table, SG.num_gens, true)){
    partial_iso i={SG,S,table};
    if(i.surjective()&&i.morphism())
      res.push_back({i.table});
  }
  return res;
}

vector<semigroup>semigps;
vector<pair<partial_iso,int>>ref_semigps;
pair<partial_iso,int> find_iso_grp(const sub_generating_set&dom){
  for(int i=0;i<semigps.size();++i){
    auto o=find_iso(dom,semigps[i]);
    if(o) return {*o,i};
  }
  cerr<<"Internal error: Did not find isomorphic copy\n";
  cerr<<dom.table<<dom.as_set<<"/"<<dom.num_gens<<endl;
  exit(1);
}


struct action {
  partial_iso iso;
  int size=-1;
  vector<H>table={};

  const sub_generating_set&grp()const {
    return iso.dom;
  }
  H mul(V v, H h)const {
    return table[v.val*size+h.val];
  }
  H mul(vector<V>v, H h)const {
    for(int i=int(v.size())-1;i>=0;--i)
      h=mul(v[i],h);
    return h;
  }

  bool is_action()const {
    for(V v={0};v.val<grp().size;++v)
      for(V w={0};w.val<grp().size;++w)
	for(H h={0};h.val<size;++h)
	  if(mul(v,mul(w,h))!=mul(grp().mul(v,w),h))
	    return false;
    return true;
  }

  void init_subgroup(const action&from) {
    size=from.size;
    table.resize(grp().size*size);
    for(V v={0};v.val<grp().size;++v)
      if(grp().mem_set[v])
	for(H h={0};h.val<size;++h)
	  table[v.val*size+h.val]=from.mul(iso.eval(v),h);
  }
  void extend(const vector<H>&new_gen) {
    V gen={grp().as_set.max()};
    for(H h={0};h.val<size;++h)
      table[gen.val*size+h.val]=new_gen[h.val];
    for(V v={0};v.val<grp().size;++v)
      if(!grp().mem_set[v]&&v!=gen)
	for(H h={0};h.val<size;++h)
	  table[v.val*size+h.val]=mul(grp().rep(v),h);
  }
  vector<action>extensions()const {
    vector<action>res;
    for(auto table: comb_ran<H>(id_map<H>(size).table, size, false)){
      action a=*this;
      a.extend(table);
      if(a.is_action())res.push_back(a);
    }
    return res;
  }

  bool isomorphic(const action&a)const {
    if(size!=a.size)return false;
    comb_ran<H>perms(id_map<H>(size).table, size, true);
    for(auto f: perms){
      bool equivariant=true;
      for(V v={0};v.val<grp().size;++v)
	for(H h={0};h.val<size;++h)
	  if(mul(v,f[h.val])!=f[a.mul(v,h).val])
	    equivariant=false;
      if(equivariant)return true;
    }
    return false;
  }
  
  static action empty_on(int size) {
    return {partial_iso::empty, size, {}};
  }
};

struct wilke_alg : action {
  vector<H>table;

  H pow(V v)const {
    return table[v.val];
  }

  bool axiom()const {
    for(V v={0};v.val<grp().size;++v)
      for(V w={0};w.val<grp().size;++w)
	if(pow(grp().mul(v,w))!=mul(v,pow(grp().mul(w,v))))
	  return false;
    return true;
  }

  void extend(const vector<H>&idemp){
    table.resize(grp().size);
    subset i=grp().idempotents();
    int gi=0;
    for(auto it=i.begin();it!=i.end();++gi,++it)
      table[(*it).val]=idemp[gi];
    for(V v={0};v.val<grp().size;++v)
      table[v.val]=pow(grp().idem_pow(v));
  }

  bool isomorphic(vector<H> otable)const {
    wilke_alg w=*this;
    w.table=otable;
    for(auto f: automorphisms(grp())){
      comb_ran<H>perms(id_map<H>(size).table, size, true);
      for(auto g: perms){
	bool good=true;
	for(V v={0};v.val<grp().size;++v)
	  for(H h={0};h.val<size;++h){
	    if(mul(f(v),g[h.val])!=g[mul(v,h).val])
	      good=false;
	    if(pow(f(v))!=g[w.pow(v).val])
	      good=false;
	  }
	if(good)return true;	
      }
    }
    return false;
  }

  bool distinguishable(V v, V w)const {
    for(H h={0};h.val<size;++h)
      if(mul(v,h)!=mul(w,h))return true;
    for(V a={0};a.val<grp().size;++a)
	if(pow(grp().mul(v,a))!=pow(grp().mul(w,a)))return true;
    return false;
  }
  //faithful Wilke algebras, see A7 on p.50 of Idziaszek's PhD thesis
  bool faithful()const {
    for(V v={0};v.val<grp().size;++v)
      for(V w={uint8_t(v.val+1)};w.val<grp().size;++w)
	if(!distinguishable(v,w))return false;
    return true;
  }

  static vector<wilke_alg>extensions(action a) {
    vector<wilke_alg>res;
    for(auto table: comb_ran<H>(id_map<H>(a.size).table, a.grp().idempotents().card(), false)){
      wilke_alg w={a,{}};
      w.extend(table);
      if(!w.axiom())goto skip;
      if(!w.faithful())goto skip;
      for(auto u:res)if(w.isomorphic(u.table))goto skip;
      res.push_back(w);
    skip:;
    }
    return res;
  }

  static wilke_alg empty_on(int size) {
    return {action::empty_on(size), {}};
  }
};

struct thin_alg : wilke_alg {
  vector<V>tableL,tableR;

  thin_alg dual() {
    return {*this, tableR, tableL};
  }

  V nodeL(H h)const {
    return tableL[h.val];
  }
  V nodeR(H h)const {
    return tableR[h.val];
  }

  bool axiom()const {
    for(H hL={0};hL.val<size;++hL.val)
      for(H hR={0};hR.val<size;++hR.val)
	if(mul(nodeL(hR),hL)!=mul(nodeR(hL),hR))
	  return false;
    return true;
  }
  
  pair<subset<V>,subset<H>>saturate(subset<V>vs, subset<H>hs)const{
    while(true){
      auto vso=vs;
      auto hso=hs;
      vs=grp().saturate(vs);
      for(auto v:vs)
	for(auto h:hso)
	  hs[mul(V{v},H{h})]=1;
      for(auto v:vs)
	hs[pow(V{v})]=1;
      for(auto h:hs)vs[nodeL(H{h})]=vs[nodeR(H{h})]=1;
      if(vso==vs&&hso==hs)return {vs,hs};
    }
  }
  bool minimal()const {
    for(H h={0};h.val<size;++h){
      subset vs=subset<V>::empty(grp().size);
      subset hs=subset<H>::singleton(size,h);
      if(saturate(vs,hs)!=std::pair{subset<V>::full(grp().size),subset<H>::full(size)})
	return false;
    }
    return true;
  }

  static vector<thin_alg>extensions(wilke_alg w) {
    vector<thin_alg>res;
    for(auto tableL: comb_ran<V>(id_map<V>(w.grp().size).table, w.size, false))
      for(auto tableR: comb_ran<V>(id_map<V>(w.grp().size).table, w.size, false)){
	thin_alg t={w,tableL,tableR};
	if(!t.axiom())goto skip;
	if(!t.minimal())goto skip;
	res.push_back(t);
      skip:;
      }
    return res;
  }
  //TODO check isomorphism and dual
  //TODO use that each h generates thin algebra and the nodeL, nodeR generate semigroup for alternative approach: then get action from nodeL, nodeR
};

vector<vector<action>>actions;
vector<vector<vector<wilke_alg>>>wilke_algs;
vector<thin_alg>thin_algs;

int main(){
  int max_v_size, max_h_size;
  cout<<"Enter size of underlying semigroup and of set acted upon"<<endl;
  std::cin>>max_v_size>>max_h_size;
  if(max_v_size>7||max_h_size>8){
    cerr<<"Not implemented"<<endl;
    return 1;
  }
  
  std::ifstream data_file("semigroups.data");
  std::ofstream actions_file("actions.data"), wilke_file("wilke.data");
  string line;
  vector<string>lines;
  lines.push_back("");//empty semigroup
  while(std::getline(data_file, line)&&line.size()<=max_v_size*max_v_size)lines.push_back(line);
  for(string s:lines){
    auto S=read_table(s);
    semigps.push_back(S);
    if(!isomorphic(S,S.opposite()))
      semigps.push_back(S.opposite());
  }

  ref_semigps.push_back({partial_iso::empty,0});
  for(int i=1;i<semigps.size();++i)
    ref_semigps.push_back(find_iso_grp({semigps[i].min_gen_set(), 1}));

  actions.resize(semigps.size());
  for(int i=0;i<=max_h_size;++i)
    actions[0].push_back(action::empty_on(i));
  for(int i=1;i<semigps.size();++i){
    auto[iso,codom_index]=ref_semigps[i];
    for(action a: actions[codom_index]){
      action b={iso};
      b.init_subgroup(a);
      for(action c: b.extensions()){
	bool iso=false;
	for(action d: actions[i])
	  if(c.isomorphic(d))iso=true;
	if(!iso)actions[i].push_back(c);
      }
    }
  }

  for(int i=0;i<semigps.size();++i){
    actions_file<<"G\n";
    for(uint8_t j=0;j<semigps[i].size;++j) {
      for(uint8_t k=0;k<semigps[i].size;++k)
	actions_file<<int(semigps[i].mul(V{j},V{k}).val)+1;
      actions_file<<"\n";
    }
    for(int a=0;a<actions[i].size();++a){
      actions_file<<"A"<<actions[i][a].size<<"\n";
      for(uint8_t j=0;j<semigps[i].size;++j){
	for(uint8_t k=0;k<actions[i][a].size;++k)
	  actions_file<<int(actions[i][a].mul(V{j},H{k}).val)+1;
	actions_file<<"\n";
      }
    }
  }

  wilke_algs.resize(semigps.size());
  for(int i=0;i<semigps.size();++i)
    for(action a: actions[i])
      wilke_algs[i].push_back(wilke_alg::extensions(a));

  for(int i=0;i<semigps.size();++i)
    for(auto w: wilke_algs[i])
      for(auto alg: w){
	wilke_file<<"G\n";
	semigroup S=semigps[i];
	for(uint8_t j=0;j<S.size;++j) {
	  for(uint8_t k=0;k<S.size;++k)
	    wilke_file<<int(S.mul(V{j},V{k}).val)+1;
	  wilke_file<<"\n";
	}
	wilke_file<<"A\n";
	action A=alg;
	for(uint8_t j=0;j<S.size;++j){
	  for(uint8_t k=0;k<A.size;++k)
	    wilke_file<<int(A.mul(V{j},H{k}).val)+1;
	  wilke_file<<"\n";
	}
	wilke_file<<"W\n";
	for(uint8_t j=0;j<S.size;++j)
	  wilke_file<<int(alg.pow(V{j}).val)+1;
	wilke_file<<"\n";
      }
}
