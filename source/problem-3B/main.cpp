
/*

O ( N (log N)^2 )

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



// a^i mod M
template<u32 MOD>
u32 powm(u32 a,u64 i) {
    if(i == 0) return 1;
    u32 r = powm<MOD>((u64)a*a%MOD,i/2);
    if(i&1) r = (u64)r*a%MOD;
    return r;
}
 

template<u32 MOD, u32 g>
void NTT(vector<u32>& A){
    int N = 1;
    while (N < A.size()) N *= 2;
    static vector<u32> exp_i_revbit_diff = { (u32)powm<MOD>(g, (MOD - 1) >> 2) };
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


template<u32 MOD, u32 g>
vector<u32> convolution(const vector<u32>& A, const vector<u32>& B){
    int Z = 1; while(Z < A.size() + B.size() - 1) Z *= 2;
    vector<u32> Ax(Z), Bx(Z);
    u64 iZ = powm<MOD>(Z, MOD - 2);
    rep(i, A.size()) Ax[i] = A[i];
    rep(i, B.size()) Bx[i] = B[i];
    NTT<MOD, g>(Ax); NTT<MOD, g>(Bx);
    rep(i,Z) Ax[i] = (u64)Ax[i] * Bx[i] % MOD;
    NTT<MOD, g>(Ax);
    reverse(Ax.begin() + 1, Ax.end());
    rep(i,Z) Ax[i] = (u64)Ax[i] * iZ % MOD;
    Ax.resize(A.size() + B.size() - 1);
    return move(Ax);
}



const u32 MOD = 998244353;
const u32 NTTzeta = 3;

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
vector<u32> M;
vector<u32> V;

vector<u32> A;
vector<u32> B;

vector<u32> ans;


vector<int> bfsbuf_dist;
void get_bfsbuf_dist(const CentroidDecomposition::BFSUnit& tree){
    if(bfsbuf_dist.size() < N) bfsbuf_dist.assign(N, 0);
    bfsbuf_dist[tree.I.front()] = 0;
    for(int i=1; i<tree.I.size(); i++){
        bfsbuf_dist[tree.I[i]] = bfsbuf_dist[tree.P[i]] + 1;
    }
}

vector<u32> bfsbuf_fIpg;
void get_bfsbuf_fIpg(const CentroidDecomposition::BFSUnit& tree){
    auto& res = bfsbuf_fIpg;
    if(res.size() < N) res.assign(N, 0);
    int g = tree.I.front();
    bfsbuf_fIpg[g] = 1;
    for(int i=1; i<tree.I.size(); i++){
        int p = tree.I[i];
        int pp = tree.P[i];
        res[p] = res[pp];
        if(pp != g) res[p] = (u64)res[p] * inv_mod(E[pp].size() - 1) % MOD;
    }
    for(int i=1; i<tree.I.size(); i++){
        int p = tree.I[i];
        res[p] = (u64)res[p] * inv_mod(E[p].size()) % MOD;
    }
}

vector<u32> bfsbuf_fOgp;
void get_bfsbuf_fOgp(const CentroidDecomposition::BFSUnit& tree){
    auto& res = bfsbuf_fOgp;
    if(res.size() < N) res.assign(N, 0);
    int g = tree.I.front();
    res[g] = 1;
    for(int i=1; i<tree.I.size(); i++){
        int p = tree.I[i];
        int pp = tree.P[i];
        res[p] = (u64)res[pp] * inv_mod(E[pp].size() - 1) % MOD;
    }
}

vector<u32> bfsbuf_fIgp;
void get_bfsbuf_fIgp(const CentroidDecomposition::BFSUnit& tree){
    auto& res = bfsbuf_fIgp;
    if(res.size() < N) res.assign(N, 0);
    int g = tree.I.front();
    res[g] = 1;
    for(int i=1; i<tree.I.size(); i++){
        int p = tree.I[i];
        int pp = tree.P[i];
        if(pp == g) res[p] = (u64)res[pp] * inv_mod(E[pp].size()) % MOD;
        else res[p] = (u64)res[pp] * inv_mod(E[pp].size() - 1) % MOD;
    }
}

vector<u32> get_dist_freq_AfI(const CentroidDecomposition::BFSUnit& tree){
    int maxdist = tree.I.size();
    vector<u32> res(maxdist + 1, 0);
    for(auto p : tree.I){
        int d = bfsbuf_dist[p];
        res[d] = (res[d] + (u64)A[p] * bfsbuf_fIpg[p]) % MOD;
    }
    return res;
}
vector<u32> get_dist_freq_BfO(const CentroidDecomposition::BFSUnit& tree){
    int maxdist = tree.I.size();
    vector<u32> res(maxdist + 1, 0);
    for(auto p : tree.I){
        int d = bfsbuf_dist[p];
        res[d] = (res[d] + (u64)B[p] * bfsbuf_fOgp[p]) % MOD;
    }
    return res;
}

vector<u32> subtree_query(const CentroidDecomposition::BFSUnit& tree){
    int g = tree.I[0];
    int n = tree.I.size();
    auto xA = get_dist_freq_AfI(tree); xA[0] = 0;
    xA.resize(n+1, 0);
    reverse(xA.begin(), xA.end());
    auto xC = vector_clip(convolution<MOD, NTTzeta>(xA, vector_clip(V, 0, n*2+1)), n);
    vector<u32> res(n, 0);
    for(int i=1; i<tree.I.size(); i++){
        int p = tree.I[i];
        int d = bfsbuf_dist[p];
        res[i] = (res[i] + (u64)xC[d] * bfsbuf_fOgp[p] % MOD * B[p]) % MOD;
        res[i] = (res[i] + (u64)A[g] * B[p] % MOD * bfsbuf_fIgp[p] % MOD * V[bfsbuf_dist[p]]) % MOD;
    }
    for(int i=0; i<tree.I.size(); i++){
        int p = tree.I[i];
        int d = bfsbuf_dist[p];
        res[0] = (res[0] + (u64)A[p] * B[g] % MOD * bfsbuf_fIpg[p] % MOD * V[bfsbuf_dist[p]]) % MOD;
    }
    return res;
}

vector<u32> subtree_query_2(const CentroidDecomposition::BFSUnit& tree){
    int n = tree.I.size() + 1;
    auto xA = get_dist_freq_AfI(tree);
    xA.resize(n+1, 0);
    reverse(xA.begin(), xA.end());
    auto xC = vector_clip(convolution<MOD, NTTzeta>(xA, vector_clip(V, 0, n*2+1)), n);
    vector<u32> res(tree.I.size(), 0);
    for(int i=0; i<tree.I.size(); i++){
        int p = tree.I[i];
        int d = bfsbuf_dist[p];
        res[i] = (res[i] + (u64)xC[d] * bfsbuf_fOgp[p] % MOD * B[p]) % MOD;
    }
    return res;
}


int main() {
    cin >> N;

    M.resize(N);
    for(int i=0; i<N; i++) cin >> M[i];
    V.assign(N*2+2, 0); // extend
    for(int i=0; i<=N; i++) cin >> V[i];

    E.resize(N);
    rep(i,N-1){
        int u,v; cin >> u >> v; u--; v--;
        E[u].push_back(v);
        E[v].push_back(u);
    }

    inv_table(N);

    auto centroid_decomposition = CentroidDecomposition(E);

    A = M;
    B.assign(N, 1);

    ans.assign(N, 0);

    for(int s=0; s<N; s++){
        int dep_s = centroid_decomposition.cdep[s];
        auto bfs_s = centroid_decomposition.bfs_layer(s, dep_s);

        get_bfsbuf_dist(bfs_s);
        get_bfsbuf_fIpg(bfs_s);
        get_bfsbuf_fOgp(bfs_s);
        get_bfsbuf_fIgp(bfs_s);
        
        vector<u32> sigma_s = subtree_query(bfs_s);
        for(int i=0; i<bfs_s.I.size(); i++) ans[bfs_s.I[i]] = (ans[bfs_s.I[i]] + sigma_s[i]) % MOD;
        
        for(int nx : E[s]) if(centroid_decomposition.cdep[nx] > dep_s){
            CentroidDecomposition::BFSUnit bfs_nx = centroid_decomposition.bfs_layer(nx, dep_s+1);
            vector<u32> sigma_nx = subtree_query_2(bfs_nx);
            for(int i=0; i<bfs_nx.I.size(); i++) ans[bfs_nx.I[i]] = (ans[bfs_nx.I[i]] + MOD - sigma_nx[i]) % MOD;
        }
    }

    for(int i=0; i<N; i++) cout << ans[i] << "\n";
    return 0;
}
