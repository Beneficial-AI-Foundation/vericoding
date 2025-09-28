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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, teams: Vec<(i8, i8)>) -> (result: Vec<(i8, i8)>)
  requires valid_input(n as int, teams@.map_values(|t: (i8, i8)| (t.0 as int, t.1 as int)))
  ensures valid_output(n as int, teams@.map_values(|t: (i8, i8)| (t.0 as int, t.1 as int)), result@.map_values(|r: (i8, i8)| (r.0 as int, r.1 as int)))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [correctly use `n` and `home_count_spec` as u8 types where appropriate] */
{
    let mut result_vec: Vec<(i8, i8)> = Vec::new();

    let mut i: i8 = 0;
    while i < n
        invariant
            0 <= i,
            i <= n,
            result_vec.len() == i as nat,
            forall|k: int| 0 <= k < i as int ==> {
                let current_team_away_k = teams@[k].1 as int;
                let home_count_k = (Set::new(|j: int| 0 <= j < n as int && teams@[j].0 == current_team_away_k)).len();
                let home_score_k = (n as int - 1) + home_count_k as int;
                let away_score_k = (n as int - 1) - home_count_k as int;
                #[trigger] result_vec@[k].0 as int == home_score_k &&
                #[trigger] result_vec@[k].1 as int == away_score_k
            },
    decreases (n - i) as int
    {
        let current_team_away_spec = teams@[i as int].1 as int;
        let home_count_spec = (Set::new(|j: int| 0 <= j < n as int && teams@[j].0 == current_team_away_spec)).len();
        
        let home_score_spec: i8 = (n - 1) + home_count_spec as i8;
        let away_score_spec: i8 = (n - 1) - home_count_spec as i8;
        
        result_vec.push((home_score_spec, away_score_spec));
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}

fn main() {}