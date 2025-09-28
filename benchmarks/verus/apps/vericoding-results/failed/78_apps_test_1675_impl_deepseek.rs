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
/* helper modified by LLM (iteration 5): Fixed type conversions and function calls */
proof fn lemma_home_count_valid(n: int, teams: Seq<(int, int)>, i: int)
    requires
        n >= 2,
        teams.len() == n,
        forall|k: int| 0 <= k < n ==> #[trigger] teams[k].0 != #[trigger] teams[k].1,
        0 <= i < n
    ensures
        team_home_count(teams, teams[i].1) <= n - 1,
        team_home_count(teams, teams[i].1) >= 0
{
}

spec fn team_home_count(teams: Seq<(int, int)>, team: int) -> int
{
    Set::new(|j: int| 0 <= j < teams.len() && teams[j].0 == team).len() as int
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, teams: Vec<(i8, i8)>) -> (result: Vec<(i8, i8)>)
  requires valid_input(n as int, teams@.map_values(|t: (i8, i8)| (t.0 as int, t.1 as int)))
  ensures valid_output(n as int, teams@.map_values(|t: (i8, i8)| (t.0 as int, t.1 as int)), result@.map_values(|r: (i8, i8)| (r.0 as int, r.1 as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by adding proper conversions and addressing type issues */
    let mut result = Vec::with_capacity(n as usize);
    let mut i: usize = 0;
    
    let seq_teams = teams@.map_values(|t: (i8, i8)| (t.0 as int, t.1 as int));
    
    while i < n as usize
        invariant
            i <= n as usize,
            forall|j: int| 0 <= j < i ==> {
                let home_count = team_home_count(seq_teams, seq_teams[j as int].1);
                result[j].0 == (n - 1) + (home_count as i8),
                result[j].1 == (n - 1) - (home_count as i8)
            },
            result@.len() == i
    {
        proof {
            lemma_home_count_valid(n as int, seq_teams, i as int);
        }
        let home_count = team_home_count(seq_teams, seq_teams[i as int].1);
        let wins = (n - 1) + (home_count as i8);
        let losses = (n - 1) - (home_count as i8);
        result.push((wins, losses));
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}