// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_occurrences(result: Seq<usize>, player: usize) -> nat 
    decreases result.len()
{
    if result.len() == 0 {
        0
    } else {
        let count_rest = count_occurrences(result.drop_first(), player);
        if result[0] == player {
            count_rest + 1
        } else {
            count_rest
        }
    }
}

spec fn no_consecutive_same(result: Seq<usize>) -> bool 
    decreases result.len()
{
    if result.len() <= 1 {
        true
    } else {
        result[0] != result[1] && no_consecutive_same(result.drop_first())
    }
}

fn assign_bowlers(n: usize, k: usize, l: usize) -> (result: Vec<usize>)
    requires n > 0 && k > 0 && l > 0,
    ensures
        /* Valid assignment case */
        (result.len() > 0 ==> (
            result.len() == n &&
            forall|x: usize| #[trigger] result@.contains(x) ==> (1 <= x && x <= k) &&
            no_consecutive_same(result@) &&
            forall|player: usize| 1 <= player <= k ==> #[trigger] count_occurrences(result@, player) <= (l as nat)
        )) &&
        /* Impossible case conditions */
        (result.len() == 0 ==> (k * l < n || (k == 1 && n > 1)))
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-code>


/* Apps difficulty: interview */
/* Assurance level: unguarded */

}
fn main() {
    // let result1 = assign_bowlers(4, 3, 2);
    // println!("{:?}", result1);  // Expected: [1, 2, 3, 2]
    
    // let result2 = assign_bowlers(5, 4, 1);
    // println!("{:?}", result2);  // Expected: []
    
    // let result3 = assign_bowlers(3, 3, 1);
    // println!("{:?}", result3);  // Expected: [1, 2, 3]
}