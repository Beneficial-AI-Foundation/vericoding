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
/* helper modified by LLM (iteration 5): count_prefix_matches using nat n_prefix to avoid int/nat mismatch */
spec fn count_prefix_matches(teams: Seq<(int, int)>, n_prefix: nat, x: int) -> nat
    requires
        n_prefix <= teams.len(),
    decreases
        n_prefix,
{
    if n_prefix == 0 {
        0
    } else {
        let prev = count_prefix_matches(teams, n_prefix - 1, x);
        if #[trigger] teams[n_prefix - 1].0 == #[trigger] x { prev + 1 } else { prev }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, teams: Vec<(i8, i8)>) -> (result: Vec<(i8, i8)>)
  requires valid_input(n as int, teams@.map_values(|t: (i8, i8)| (t.0 as int, t.1 as int)))
  ensures valid_output(n as int, teams@.map_values(|t: (i8, i8)| (t.0 as int, t.1 as int)), result@.map_values(|r: (i8, i8)| (r.0 as int, r.1 as int)))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): compute home/away counts per team using explicit loops */
  let mut result: Vec<(i8, i8)> = Vec::new();
  let total: usize = teams.len();
  let mut i: usize = 0;
  while i < total
      invariant
          result.len() == i,
          i <= total,
      decreases (total as int) - (i as int)
  {
      let mut cnt: i8 = 0;
      let mut j: usize = 0;
      while j < total
          invariant
              j <= total,
          decreases (total as int) - (j as int)
      {
          if teams.get(j).unwrap().0 == teams.get(i).unwrap().1 {
              cnt = cnt + 1;
          }
          j = j + 1;
      }
      let home: i8 = (n - 1) + cnt;
      let away: i8 = (n - 1) - cnt;
      result.push((home, away));
      i = i + 1;
  }
  result
}
// </vc-code>


}

fn main() {}