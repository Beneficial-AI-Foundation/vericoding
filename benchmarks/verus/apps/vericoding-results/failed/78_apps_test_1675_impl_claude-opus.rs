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
{
    /* code modified by LLM (iteration 4): added decreases clause to outer loop */
    let mut result: Vec<(i8, i8)> = Vec::new();
    let mut i: usize = 0;
    while i < n as usize
        invariant
            n >= 2,
            teams.len() == n as usize,
            valid_input(n as int, teams@.map_values(|t: (i8, i8)| (t.0 as int, t.1 as int))),
            i <= n as usize,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j].0 + #[trigger] result@[j].1 == 2 * (n as int - 1),
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j].0 >= n as int - 1,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j].1 >= 0,
            forall|j: int| 0 <= j < i ==> {
                let home_count = (Set::new(|k: int| 0 <= k < n as int && #[trigger] teams@.map_values(|t: (i8, i8)| (t.0 as int, t.1 as int))[k].0 == #[trigger] teams@.map_values(|t: (i8, i8)| (t.0 as int, t.1 as int))[j].1)).len() as int;
                #[trigger] result@[j].0 == ((n as int - 1) + home_count) as i8 &&
                #[trigger] result@[j].1 == ((n as int - 1) - home_count) as i8
            },
        decreases n as usize - i
    {
        let mut home_count: i8 = 0;
        let mut j: usize = 0;
        while j < n as usize
            invariant
                n >= 2,
                teams.len() == n as usize,
                valid_input(n as int, teams@.map_values(|t: (i8, i8)| (t.0 as int, t.1 as int))),
                i < n as usize,
                j <= n as usize,
                home_count >= 0,
                home_count <= j as i8,
                home_count as int == (Set::new(|k: int| 0 <= k < j as int && #[trigger] teams@[k as int].0 == #[trigger] teams@[i as int].1)).len() as int,
            decreases n as usize - j
        {
            if teams[j].0 == teams[i].1 {
                home_count = home_count + 1;
            }
            j = j + 1;
        }
        
        let home_games = (n - 1) + home_count;
        let away_games = (n - 1) - home_count;
        result.push((home_games, away_games));
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}