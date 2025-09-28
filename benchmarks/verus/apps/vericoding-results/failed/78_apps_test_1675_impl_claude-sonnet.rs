// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, teams: Seq<(int, int)>) -> bool {
  n >= 2 && teams.len() == n &&
  (forall|i: int| 0 <= i < n ==> #[trigger] teams[i].0 != #[trigger] teams[i].1) &&
  (forall|i: int| 0 <= i < n ==> 
    (Set::new(|j: int| 0 <= j < n && #[trigger] teams[j].0 == #[trigger] teams[i].1)).len() <= (n - 1) as nat)
}

spec fn valid_output(n: int, teams: Seq<(int, int)>, result: Seq<(int, int)>) -> bool
  recommends teams.len() == n
{
  result.len() == n &&
  (forall|i: int| 0 <= i < n ==> #[trigger] result[i].0 + #[trigger] result[i].1 == 2 * (n - 1)) &&
  (forall|i: int| 0 <= i < n ==> #[trigger] result[i].0 >= n - 1) &&
  (forall|i: int| 0 <= i < n ==> #[trigger] result[i].1 >= 0) &&
  (forall|i: int| 0 <= i < n ==> {
    let home_count = (Set::new(|j: int| 0 <= j < n && #[trigger] teams[j].0 == #[trigger] teams[i].1)).len() as int;
    #[trigger] result[i].0 == (n - 1) + home_count &&
    #[trigger] result[i].1 == (n - 1) - home_count
  })
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed ensures clause syntax */
spec fn count_home_games(n: int, teams: Seq<(int, int)>, team_id: int) -> int
{
    (Set::new(|j: int| 0 <= j < n && teams[j].0 == team_id)).len() as int
}

proof fn lemma_count_home_games_valid(n: int, teams: Seq<(int, int)>, team_id: int)
    requires
        valid_input(n, teams),
        0 <= team_id < n,
    ensures
        0 <= count_home_games(n, teams, team_id) <= n - 1,
{
}

proof fn lemma_result_calculation(n: int, teams: Seq<(int, int)>, i: int)
    requires
        valid_input(n, teams),
        0 <= i < n,
    ensures
        count_home_games(n, teams, teams[i].1) >= 0,
        count_home_games(n, teams, teams[i].1) <= n - 1,
        (n - 1) + count_home_games(n, teams, teams[i].1) + (n - 1) - count_home_games(n, teams, teams[i].1) == 2 * (n - 1),
        (n - 1) + count_home_games(n, teams, teams[i].1) >= n - 1,
        (n - 1) - count_home_games(n, teams, teams[i].1) >= 0,
{
    let home_count = count_home_games(n, teams, teams[i].1);
    lemma_count_home_games_valid(n, teams, teams[i].1);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, teams: Vec<(i8, i8)>) -> (result: Vec<(i8, i8)>)
  requires valid_input(n as int, teams@.map_values(|t: (i8, i8)| (t.0 as int, t.1 as int)))
  ensures valid_output(n as int, teams@.map_values(|t: (i8, i8)| (t.0 as int, t.1 as int)), result@.map_values(|r: (i8, i8)| (r.0 as int, r.1 as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed usize indexing for Vec access */
    let mut result = Vec::new();
    let mut idx = 0;
    
    while idx < n
        invariant
            0 <= idx <= n,
            result.len() == idx,
            valid_input(n as int, teams@.map_values(|t: (i8, i8)| (t.0 as int, t.1 as int))),
            forall|k: int| 0 <= k < idx ==> {
                let teams_spec = teams@.map_values(|t: (i8, i8)| (t.0 as int, t.1 as int));
                let result_spec = result@.map_values(|r: (i8, i8)| (r.0 as int, r.1 as int));
                let home_count = count_home_games(n as int, teams_spec, teams_spec[k].1);
                result_spec[k].0 == (n as int - 1) + home_count &&
                result_spec[k].1 == (n as int - 1) - home_count
            },
    {
        let team_id = teams[idx as usize].1;
        let mut home_count = 0i8;
        let mut j = 0;
        
        while j < n
            invariant
                0 <= j <= n,
                0 <= idx < n,
                team_id == teams[idx as usize].1,
                home_count == (Set::new(|k: int| 0 <= k < j && teams@[k as int].0 == team_id as int)).len() as i8,
        {
            if teams[j as usize].0 == team_id {
                home_count = home_count + 1;
            }
            j = j + 1;
        }
        
        let wins = (n - 1) + home_count;
        let losses = (n - 1) - home_count;
        
        proof {
            let teams_spec = teams@.map_values(|t: (i8, i8)| (t.0 as int, t.1 as int));
            lemma_result_calculation(n as int, teams_spec, idx as int);
        }
        
        result.push((wins, losses));
        idx = idx + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}