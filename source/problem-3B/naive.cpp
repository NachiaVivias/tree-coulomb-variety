
/*

O ( N^2 )

*/

#include <iostream>
#include <vector>
#include <algorithm>
#include <cassert>
using namespace std;
using i32 = int;
using u32 = unsigned int;
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
vector<u64> M;
vector<u64> V;

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

vector<u64> get_fI_table(int s){
    vector<u64> res(N, 0);
    vector<int> visited(N, 0);
    vector<int> I = {s};
    res[s] = 1;
    visited[s] = 1;
    for(int i=0; i<I.size(); i++){
        int p = I[i];
        int num_way = 0;
        for(int e : E[p]) if(visited[e] == 0) num_way++;
        for(int e : E[p]) if(visited[e] == 0){
            res[e] = res[p] * inv_mod(num_way) % MOD;
            visited[e] = 1;
            I.push_back(e);
        }
    }
    return res;
}


int main() {
    cin >> N;

    M.resize(N);
    for(int i=0; i<N; i++) cin >> M[i];
    V.resize(N+1);
    for(int i=0; i<=N; i++) cin >> V[i];

    E.resize(N);
    for(int i=0; i<N-1; i++){
        int u, v; cin >> u >> v; u--; v--;
        E[u].push_back(v);
        E[v].push_back(u);
    }

    inv_table(N);

    vector<u64> ans(N,0);
    for(int s=0; s<N; s++){
        auto dist = get_dist_table(s);
        auto fI = get_fI_table(s);
        for(int i=0; i<N; i++) ans[i] = (ans[i] + M[s] * fI[i] % MOD * V[dist[i]]) % MOD;
    }
    
    for(int i=0; i<N; i++) cout << ans[i] << "\n";
    
    return 0;
}
