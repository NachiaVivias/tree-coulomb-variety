
/*

O ( N^2 )

*/

#include <iostream>
#include <vector>
#include <algorithm>
#include <cassert>
using namespace std;
using i32 = int;
using u32 = unsigned;
using i64 = long long;
using u64 = unsigned long long;
#define rep(i,n) for(int i=0; i<(n); i++)


const u64 MOD = 998244353;

vector<u64> invs;

u64 pow_mod(u64 a, u64 i){
    u64 r = 0;
    while(i){
        if(i % 2){ r = r * a % MOD; }
        a = a * a % MOD;
        i /= 2;
    }
    return r;
}
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
u64 k0;
vector<u64> k0_div_dist_sq;
vector<u64> Q;

vector<int> get_dist_table(int s){
    vector<int> res(N, -1);
    vector<int> I = {s};
    res[s] = 0;
    for(int i=0; i<I.size(); i++){
        int p = I[i];
        for(int e : E[p]) if(res[e] == -1){
            res[e] = res[p] + 1;
            I.push_back(e);
        }
    }
    return res;
}


int main() {
    cin >> N;

    Q.assign(N, 0);

    E.resize(N);
    for(int i=0; i<N-1; i++){
        int u, v; cin >> u >> v; u--; v--;
        E[u].push_back(v);
        E[v].push_back(u);
    }

    inv_table(N);

    k0 = 1;
    for(int i=1; i<=N; i++) k0 = k0 * i % MOD;
    k0 = k0 * k0 % MOD;
    k0_div_dist_sq.assign(N, k0);
    for(int i=0; i<N; i++) k0_div_dist_sq[i] = k0_div_dist_sq[i] * inv_mod(i+1) % MOD * inv_mod(i+1) % MOD;

    int K; cin >> K;
    
    for(int query_idx=0; query_idx<K; query_idx++){
        int t; cin >> t;
        if(t == 1){
            int p; u64 q; cin >> p >> q; p--;
            Q[p] = q;
        }
        else if(t == 2){
            int p; cin >> p; p--;
            auto dist = get_dist_table(p);
            u64 ans = 0;
            for(int i=0; i<N; i++) ans = (ans + Q[i] * k0_div_dist_sq[dist[i]]) % MOD;
            cout << ans << "\n";
        }
    }
    
    return 0;
}
