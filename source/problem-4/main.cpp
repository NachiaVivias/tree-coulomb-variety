
/*

O ( N (log N)^4 )

*/

#include <iostream>
#include <vector>
#include <algorithm>
#include <cassert>
using namespace std;
using i64 = long long;
using u64 = unsigned long long;
using i32 = int;
using u32 = unsigned int;
#define rep(i,n) for(int i=0; i<(n); i++)



template<u32 MOD>
struct PrimitiveRoot{
    static constexpr u64 powm(u64 a, u64 i) {
        u64 res = 1, aa = a;
        while(i){
            if(i & 1) res = res * aa % MOD;
            aa = aa * aa % MOD;
            i /= 2;
        }
        return res;
    }
    static constexpr bool examine_val(u32 g){
        u32 t = MOD - 1;
        for(u64 d=2; d*d<=t; d++) if(t % d == 0){
            if(powm(g, (MOD - 1) / d) == 1) return false;
            while(t % d == 0) t /= d;
        }
        if(t != 1) if(powm(g, (MOD - 1) / t) == 1) return false;
        return true;
    }
    static constexpr u32 get_val(){
        for(u32 x=2; x<MOD; x++) if(examine_val(x)) return x;
        return 0;
    }
    static const u32 val = get_val();
};

 

template<u32 MOD>
u32 powm(u32 a, u32 i) {
    u64 res = 1, aa = a;
    while(i){
        if(i & 1) res = res * aa % MOD;
        aa = aa * aa % MOD;
        i /= 2;
    }
    return res;
}


template<u32 MOD, u32 g>
void NTT(vector<u32>& A){
    int N = 1;
    while (N < A.size()) N *= 2;
    static vector<u32> exp_i_revbit_diff = { powm<MOD>(g, (MOD - 1) >> 2) };
    for(int i=exp_i_revbit_diff.size(); (1<<(i+1))<N; i++){
        u64 diffdiff = powm<MOD>(g, (MOD - 1) / 2 + ((MOD - 1) >> (i+2)) * 3);
        exp_i_revbit_diff.push_back(diffdiff);
    }
    for (int i = 1; i < N; i <<= 1) {
        u64 q = 1;
        int maxk = N / i / 2;
        for (int j = 0; j < i; j++) {
            int off = j * maxk * 2;
            for (int k = off; k < off + maxk; k++) {
                u32 l = A[k];
                u32 r = A[k + maxk] * q % MOD;
                A[k] = min(l + r - MOD, l + r);
                A[k + maxk] = min(l - r, l + MOD - r);
            }
            if(j+1 != i) for(int d=0; ; d++) if(!(j&(1<<d))){
                q = q * exp_i_revbit_diff[d] % MOD;
                break;
            }
        }
    }
    for (int i = 0, j = 0; j < N; j++) {
        if (i < j) swap(A[i], A[j]);
        for (int k = N >> 1; k > (i ^= k); k >>= 1);
    }
}


template<u32 MOD>
vector<u32> Convolution(const vector<u32>& A, const vector<u32>& B){
    constexpr u32 g = PrimitiveRoot<MOD>::val;
    int Z = 1; while(Z < A.size() + B.size() - 1) Z *= 2;
    vector<u32> Ax(Z), Bx(Z);
    u64 iZ = powm<MOD>(Z, MOD - 2);
    for(int i=0; i<A.size(); i++) Ax[i] = A[i];
    for(int i=0; i<B.size(); i++) Bx[i] = B[i];
    NTT<MOD, g>(Ax); NTT<MOD, g>(Bx);
    for(int i=0; i<Z; i++) Ax[i] = (u64)Ax[i] * Bx[i] % MOD;
    NTT<MOD, g>(Ax);
    reverse(Ax.begin() + 1, Ax.end());
    for(int i=0; i<Z; i++) Ax[i] = (u64)Ax[i] * iZ % MOD;
    Ax.resize(A.size() + B.size() - 1);
    return Ax;
}




template<u32 MOD>
vector<u32> PowSumFPS(const vector<u32>& A, int n){
    if(A[0] != 0){ cerr << "PowSumFPS : undefined for A[0] != 0 !!!!!" << endl; exit(9); }
    constexpr u32 g = PrimitiveRoot<MOD>::val;
    if(n == 0){ return {}; }
    if(n == 1){ return { 1 }; }
    int N = 1; while(N<n) N*=2;
    int hN = N/2;
    vector<u32> hInv = PowSumFPS<MOD>(A,hN);
    vector<u32> tgA(N,0);
    for(int i=0; i<min(N,(int)A.size()); i++) tgA[i] = A[i];
    u64 ig = powm<MOD>(g,MOD-2);
    NTT<MOD,g>(tgA);
    vector<u32> htInv(N,0);
    for(int i=0; i<hN; i++) htInv[i] = hInv[i];
    NTT<MOD,g>(htInv);
    vector<u32> R(N);
    for(int i=0; i<N; i++) R[i] = (u64)tgA[i] * htInv[i] % MOD;
    NTT<MOD,g>(R); reverse(R.begin()+1, R.end());
    for(int i=0; i<hN; i++) R[i] = R[hN+i];
    for(int i=hN; i<N; i++) R[i] = 0;
    NTT<MOD,g>(R);
    u64 iNN = powm<MOD>((u64)N*N%MOD,MOD-2);
    for(int i=0; i<N; i++) R[i] = (u64)R[i] * htInv[i] % MOD * iNN % MOD;
    NTT<MOD,g>(R); reverse(R.begin()+1, R.end());
    hInv.resize(n,0);
    for(int i=hN; i<n; i++) hInv[i] = R[i-hN];
    return hInv;
}


template<u32 MOD>
vector<u32> InvFPS(const vector<u32>& A, int n){
    if(A[0] == 0){ cerr << "InvFPS : inverse of 0 !!!!!" << endl; exit(9); }
    u64 iA0 = (A[0] == 1 ? 1 : powm<MOD>(A[0],MOD-2));
    vector<u32> xA(min(n,(int)A.size()));
    for(int i=0; i<xA.size(); i++) xA[i] = (MOD - A[i]) * iA0 % MOD;
    xA[0] = 0;
    xA = PowSumFPS<MOD>(xA,n);
    for(int i=0; i<xA.size(); i++) xA[i] = xA[i] * iA0 % MOD;
    return xA;
}


template<u32 MOD>
pair<vector<u32>, vector<u32>> PolynomialDivision(vector<u32> A, vector<u32> D, bool do_get_remainder = true){
    if(A.empty()){ return make_pair(vector<u32>(), vector<u32>()); }
    while(!D.empty() && D.back() == 0) D.pop_back();
    if(D.empty()){ cerr << "PolynomialDivision : division by 0 !!!!!" << endl; exit(9); }
    if(A.size() < D.size()){ return make_pair(vector<u32>(), move(A)); }
    reverse(D.begin(), D.end());

    int n = A.size();
    auto invD = InvFPS<MOD>(D, n - D.size() + 1);

    reverse(A.begin(), A.end());
    auto tmp = Convolution<MOD>(A, invD);
    tmp.resize(n - D.size() + 1);
    vector<u32> ans1(n - D.size() + 1);
    for(int i=0; i<ans1.size(); i++) ans1[ans1.size()-1-i] = tmp[i];
    if(!do_get_remainder) return make_pair(move(ans1), vector<u32>());
    if(D.size() == 1) return make_pair(move(ans1), vector<u32>());
    tmp = Convolution<MOD>(tmp, D);
    vector<u32> ans2(D.size() - 1);
    for(int i=0; i<D.size()-1; i++) ans2[i] = A[n-1-i] + MOD - tmp[n-1-i];
    for(int i=0; i<D.size()-1; i++) if(ans2[i] >= MOD) ans2[i] -= MOD;
    while(!ans2.empty() && ans2.back() == 0) ans2.pop_back();
    return make_pair(move(ans1), move(ans2));
}



template<u32 MOD>
vector<u32> MultipointEvaluation(vector<u32> A, vector<u32> x){
    int segtree_n = 1;
    while(segtree_n < x.size()) segtree_n *= 2;
    vector<vector<u32>> divtree(segtree_n * 2);
    for(int i=0; i<segtree_n; i++) divtree[segtree_n + i] = { 1 };
    for(int i=0; i<x.size(); i++) divtree[segtree_n + i * segtree_n / x.size()] = { MOD-x[i], 1 };
    for(int i=segtree_n-1; i>=1; i--) divtree[i] = Convolution<MOD>(divtree[i*2], divtree[i*2+1]);
    vector<vector<u32>> remtree(segtree_n * 2);
    remtree[1] = PolynomialDivision<MOD>(A, divtree[1]).second;
    for(int i=2; i<segtree_n*2; i++) if(divtree[i].size() > 1) remtree[i] = PolynomialDivision<MOD>(remtree[i/2], divtree[i]).second;
    vector<u32> res(x.size());
    for(int i=0; i<x.size(); i++) res[i] = remtree[segtree_n + i * segtree_n / x.size()][0];
    return res;
}




template<class E>
vector<E> vector_concat(const vector<E>& a, const vector<E>& b){
    vector<E> res(a.size() + b.size());
    for(int i=0; i<a.size(); i++) res[i] = a[i];
    for(int i=0; i<b.size(); i++) res[a.size() + i] = b[i];
    return res;
}

template<class E>
vector<E> vector_clip(const vector<E>& a, int left, int length = -1){
    if(a.size() <= left) return vector<E>();
    if(length == -1) length = a.size();
    length = min(length, (int)a.size() - left);
    vector<E> res(length);
    for(int i=0; i<length; i++) res[i] = a[i+left];
    return res;
}


struct CentroidDecomposition {
    int n;
    vector<vector<int>> E;
    vector<int> cdep;
    vector<int> cp;
    vector<int> cbfs;
    int maxdep;
    CentroidDecomposition(vector<vector<int>> edges) {
        E = move(edges);
        n = E.size();
        vector<int> Z(n, 1);
        {
            vector<int> P(n, -1);
            vector<int> I = { 0 };
            rep(i, I.size()) {
                int p = I[i];
                for (int e : E[p]) if (P[p] != e) {
                    P[e] = p;
                    I.push_back(e);
                }
            }
            for (int i = n - 1; i >= 1; i--) Z[P[I[i]]] += Z[I[i]];
        }
        cp.assign(n, -1);
        cdep.assign(n, 0);
        vector<pair<int, int>> I = { {0,-1} };
        rep(i, I.size()) {
            int s = I[i].first;
            int par = I[i].second;
            while (true) {
                int nx = -1;
                for (int e : E[s]) if (Z[e] * 2 > Z[s]) nx = e;
                if (nx == -1) break;
                Z[s] -= Z[nx];
                Z[nx] += Z[s];
                s = nx;
            }
            cbfs.push_back(s);
            Z[s] = 0;
            if (par != -1) {
                cdep[s] = cdep[par] + 1;
                cp[s] = par;
            }
            for (int e : E[s]) if (Z[e] != 0) {
                I.push_back(make_pair(e, s));
            }
        }
        maxdep = 0;
        for (int a : cdep) maxdep = max(maxdep, a);
    }

    struct BFSUnit {
        vector<int> I;
        vector<int> P;
    };
    BFSUnit bfs_layer(int s, int layer) {
        BFSUnit res;
        if (cdep[s] < layer) return res;
        res.I.push_back(s);
        res.P.push_back(-1);
        rep(i, res.I.size()) {
            int p = res.I[i];
            for (int e : E[p]) if (res.P[i] != e) {
                if (cdep[e] < layer) continue;
                res.I.push_back(e);
                res.P.push_back(p);
            }
        }
        return res;
    }
};



const u32 MOD = 998244353;


// time : O( k (log k)^2 + q (log q)^2 + q log mod )
struct Problem4_1{
    int k;
    int q;
    vector<u32> C;
    vector<u32> D;
    vector<u32> X;
    vector<u32> ans;

    Problem4_1(){
        k = 0;
        q = 0;
    }

    void add_term(u32 c, u32 d){
        k++;
        C.push_back(c);
        D.push_back(d);
    }
    int add_query(u32 x){
        q++;
        X.push_back(x);
        return q-1;
    }

    void solve(){
        assert(C.size() == k);
        assert(D.size() == k);
        assert(X.size() == q);
        ans.resize(q);
        if(q == 0) return;
        if(k == 0){ ans = vector<u32>(q,0); return; }
        vector<vector<u32>> segtree_a(k*2); // numerator
        vector<vector<u32>> segtree_d(k*2); // denominator
        for(int i=0; i<k; i++){
            segtree_a[k+i] = { C[i] };
            segtree_d[k+i] = { (u32)((u64)D[i] * D[i] % MOD), (u32)((u64)D[i] * 2 % MOD), (u32)1 };
        }
        for(int i=k-1; i>=1; i--){
            segtree_d[i] = Convolution<MOD>(segtree_d[i*2], segtree_d[i*2+1]);
            auto a_0 = Convolution<MOD>(segtree_d[i*2], segtree_a[i*2+1]);
            auto a_1 = Convolution<MOD>(segtree_a[i*2], segtree_d[i*2+1]);
            if(a_0.size() < a_1.size()) swap(a_0, a_1);
            for(int i=0; i<a_1.size(); i++) a_0[i] = (a_0[i] + a_1[i]) % MOD;
            segtree_a[i] = a_0;
        }

        //     ans[i] == segtree_a[i](X[i]) / segtree_d[i](X[i]) == ans_a[i] / ans_d[i]
        vector<u32> ans_a = MultipointEvaluation<MOD>(segtree_a[1], X);
        vector<u32> ans_d = MultipointEvaluation<MOD>(segtree_d[1], X);
        for(int i=0; i<q; i++) ans[i] = (u64)ans_a[i] * powm<MOD>(ans_d[i], MOD-2) % MOD;
    }
};


// time : O( q (log q)^3 )
struct Problem4_2{
    int q;
    vector<int> query_type;
    vector<pair<u32,u32>> add_queries;
    vector<u32> calc_queries;
    vector<u32> ans;

    Problem4_2(){
        q = 0;
    }

    void solve_recursive(int l, int r){
        if(r - l <= 1) return;
        int m = (l+r) / 2;

        Problem4_1 static_problem;
        vector<int> calc_ans_address(r-m);
        for(int t=l; t<m; t++) if(query_type[t] == 1) static_problem.add_term(add_queries[t].first, add_queries[t].second);
        for(int t=m; t<r; t++) if(query_type[t] == 2) calc_ans_address[t-m] = static_problem.add_query(calc_queries[t]);
        static_problem.solve();

        for(int t=m; t<r; t++) if(query_type[t] == 2) ans[t] = (ans[t] + static_problem.ans[calc_ans_address[t-m]]) % MOD;
        
        solve_recursive(l, m);
        solve_recursive(m, r);
    }

    int add_add_query(u32 c, u32 d){
        q++;
        query_type.push_back(1);
        add_queries.push_back(make_pair(c, d));
        calc_queries.push_back(0);
        return q-1;
    }

    int add_calc_query(u32 x){
        q++;
        query_type.push_back(2);
        add_queries.push_back(make_pair(0, 0));
        calc_queries.push_back(x);
        return q-1;
    }

    void solve(){
        if(q == 0) return;
        assert(query_type.size() == q);
        assert(add_queries.size() == q);
        assert(calc_queries.size() == q);
        ans.assign(q, 0);
        solve_recursive(0, q);
    }
};



vector<u64> invs;
void inv_table(u64 z){
    if(invs.empty()) invs = {1,1};
    for(int i=invs.size(); i<=z; i++) invs.push_back(MOD - (MOD / i * (u64)invs[MOD % i] % MOD) % MOD);
}
u64 inv_mod(u64 a){
    assert(a < invs.size());
    return invs[a];
}

int N;
vector<vector<int>> E;
u32 k0;

int K;
vector<int> query_type;
vector<pair<int, u32>> add_query;
vector<int> calc_query;

vector<vector<int>> queries_on_subtree;
vector<vector<int>> subtree_children;
vector<u32> ans;


vector<int> bfsbuf_dist;
void get_bfsbuf_dist(const CentroidDecomposition::BFSUnit& tree){
    if(bfsbuf_dist.size() < N) bfsbuf_dist.assign(N, 0);
    bfsbuf_dist[tree.I.front()] = 0;
    for(int i=1; i<tree.I.size(); i++){
        bfsbuf_dist[tree.I[i]] = bfsbuf_dist[tree.P[i]] + 1;
    }
}


int main() {
    
    // ------------------------
    // input graph

    cin >> N;
    
    k0 = 1;
    for(u32 i=1; i<=N; i++) k0 = (u64)k0 * i % MOD;
    k0 = (u64)k0 * k0 % MOD;

    E.resize(N);
    rep(i, N-1){
        int u,v; cin >> u >> v; u--; v--;
        E[u].push_back(v);
        E[v].push_back(u);
    }
    
    vector<u32> Q(N, 0);

    // ------------------------
    // input queries
    // translate "update" into "add"

    cin >> K;
    query_type.assign(K, 0);
    add_query.assign(K, make_pair(0,0));
    calc_query.assign(K, 0);

    rep(i, K){
        int t; cin >> t;
        query_type[i] = t;
        if(t == 1){
            int p; u32 x; cin >> p >> x; p--;
            x = (u64)x * k0 % MOD;
            x = (x + MOD - Q[p]) % MOD;
            add_query[i] = make_pair(p, x);
            Q[p] = (Q[p] + x) % MOD;
        }
        if(t == 2){
            int p; cin >> p; p--;
            calc_query[i] = p;
        }
    }

    inv_table(N);

    auto centroid_decomposition = CentroidDecomposition(E);

    // ------------------------
    // distribute queries

    queries_on_subtree.resize(N);
    for(int i=0; i<K; i++){
        if(query_type[i] == 1){
            int p = add_query[i].first;
            while(p != -1){
                queries_on_subtree[p].push_back(i);
                p = centroid_decomposition.cp[p];
            }
        }
        if(query_type[i] == 2){
            int p = calc_query[i];
            while(p != -1){
                queries_on_subtree[p].push_back(i);
                p = centroid_decomposition.cp[p];
            }
        }
    }

    subtree_children.resize(N);
    for(int i=0; i<N; i++){
        int p = centroid_decomposition.cp[i];
        if(p != -1) subtree_children[p].push_back(i);
    }

    // --------------------------------
    // solve for each subtree

    ans.assign(K, 0);
    
    for(int s=0; s<N; s++){
        get_bfsbuf_dist(centroid_decomposition.bfs_layer(s, centroid_decomposition.cdep[s]));

        Problem4_2 subproblem_s;
        for(int qi : queries_on_subtree[s]){
            if(query_type[qi] == 1) subproblem_s.add_add_query(add_query[qi].second, bfsbuf_dist[add_query[qi].first]);
            if(query_type[qi] == 2) subproblem_s.add_calc_query(bfsbuf_dist[calc_query[qi]] + 1);
        }

        subproblem_s.solve();
        for(int qii=0; qii<queries_on_subtree[s].size(); qii++){
            int qi = queries_on_subtree[s][qii];
            if(query_type[qi] == 2){
                ans[qi] = (ans[qi] + subproblem_s.ans[qii]) % MOD;
            }
        }

        for(int nx : subtree_children[s]){
            Problem4_2 subproblem_nx;
            for(int qi : queries_on_subtree[nx]){
                if(query_type[qi] == 1) subproblem_nx.add_add_query(add_query[qi].second, bfsbuf_dist[add_query[qi].first]);
                if(query_type[qi] == 2) subproblem_nx.add_calc_query(bfsbuf_dist[calc_query[qi]] + 1);
            }
            subproblem_nx.solve();
            for(int qii=0; qii<queries_on_subtree[nx].size(); qii++){
                int qi = queries_on_subtree[nx][qii];
                if(query_type[qi] == 2){
                    ans[qi] = (ans[qi] + MOD - subproblem_nx.ans[qii]) % MOD;
                }
            }
        }
    }

    // --------------------------------
    // output answers

    for(int i=0; i<K; i++){
        if(query_type[i] == 2){
            cout << ans[i] << "\n";
        }
    }

    return 0;
}
