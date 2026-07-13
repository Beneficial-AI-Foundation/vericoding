// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn can_obtain_permutation(n: usize, m: usize, perm: Vec<usize>, pairs: Vec<Vec<usize>>) -> (result: &'static str)
    requires 
        n > 0,
        m > 0,
        perm.len() == n,
        pairs.len() == m,
        forall|i: int| 0 <= i < perm.len() ==> #[trigger] perm[i] >= 1 && #[trigger] perm[i] <= n,
        forall|i: int, j: int| 0 <= i < j < perm.len() ==> #[trigger] perm[i] != #[trigger] perm[j],
        forall|i: int| 0 <= i < pairs.len() ==> #[trigger] pairs[i].len() == 2,
        forall|i: int| 0 <= i < pairs.len() ==> #[trigger] pairs[i][0] >= 1 && #[trigger] pairs[i][0] <= #[trigger] pairs[i][1] && #[trigger] pairs[i][1] <= n,
    ensures 
        result == "Possible" || result == "Impossible"
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // let result1 = can_obtain_permutation(7, 4, vec![3, 1, 2, 4, 5, 7, 6], vec![vec![1, 2], vec![4, 4], vec![6, 7], vec![2, 3]]);
    // assert(result1 == "Possible");
    
    // let result2 = can_obtain_permutation(4, 2, vec![2, 1, 3, 4], vec![vec![2, 4], vec![2, 3]]);
    // assert(result2 == "Impossible");
}