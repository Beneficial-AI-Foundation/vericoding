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
/* helper modified by LLM (iteration 2): Introduced spec function to capture the home-count set size for index i */
pub open spec fn count_set_for_i(n: int, teams: Seq<(int, int)>, i: int) -> nat
    recommends
        teams.len() == n,
        0 <= i < n,
{
    Set::new(|j: int| 0 <= j < n && #[trigger] teams[j].0 == #[trigger] teams[i].1).len()
}

/* helper modified by LLM (iteration 2): Lemma tying valid_input to the home-count upper bound for a fixed i */
proof fn lemma_home_count_upper_bound(n: int, teams: Seq<(int, int)>, i: int)
    requires
        valid_input(n, teams),
        0 <= i < n,
    ensures
        count_set_for_i(n, teams, i) <= (n - 1) as nat,
{
    proof {
        assert(valid_input(n, teams));
        // The postcondition follows by instantiating the forall in valid_input at i
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
    /* code modified by LLM (iteration 2): Removed exec 'int' variables (moved to ghost), fixed decreases to use ints, and performed computations in i8 */
    let len: usize = teams.len();
    let mut result: Vec<(i8, i8)> = Vec::with_capacity(len);

    let mut i: usize = 0;
    while i < len
        invariant
            teams@.len() as int == len as int,
            result@.len() as int == i as int,
            0 <= i as int <= len as int,
        decreases len as int - i as int
    {
        let val: i8 = teams[i].1;
        let mut count: usize = 0;
        let mut j: usize = 0;
        while j < len
            invariant
                0 <= j as int <= len as int,
                count as int == (
                    Set::new(|k: int|
                        0 <= k < j as int &&
                        #[trigger] teams@.map_values(|t: (i8, i8)| (t.0 as int, t.1 as int))[k].0 == val as int
                    ).len()
                ) as int,
            decreases len as int - j as int
        {
            if teams[j].0 == val {
                count += 1;
            }
            j += 1;
        }

        let ghost home_count_int: int = count as int;
        let ghost n_int: int = n as int;

        let base: i8 = n - 1i8;
        let r0: i8 = base + (count as i8);
        let r1: i8 = base - (count as i8);
        result.push((r0, r1));

        i += 1;
    }

    result
}
// </vc-code>


}

fn main() {}