
/*

O ( N^2 )

*/

#include <iostream>
#include <vector>
#include <algorithm>
using namespace std;
using i32 = int;
using u32 = unsigned int;
using i64 = long long;
using u64 = unsigned long long;
#define rep(i,n) for(int i=0; i<(n); i++)


u64 MOD = 998244353;


int N;
vector<vector<int>> E;

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
    E.resize(N);
    for(int i=0; i<N-1; i++){
        int u, v; cin >> u >> v; u--; v--;
        E[u].push_back(v);
        E[v].push_back(u);
    }

    vector<int> dist0 = get_dist_table(0);

    vector<u64> ans(N,0);
    for(int s=0; s<N; s++) if(dist0[s] % 2 == 0){
        auto dist = get_dist_table(s);
        for(int i=0; i<N; i++) if(dist[i] % 2 == 0) ans[dist[i]]++;
    }
    
    for(int i=0; i<N; i++) ans[i] %= MOD;
    for(int i=0; i<N; i++) cout << ans[i] << "\n";

    return 0;
}
