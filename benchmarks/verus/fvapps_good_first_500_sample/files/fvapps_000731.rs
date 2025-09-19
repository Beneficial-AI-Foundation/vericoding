// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn permutation_inverse(xs: Seq<usize>) -> Seq<usize>
    decreases xs.len()
{
    if xs.len() == 0 {
        seq![]
    } else {
        let result = Seq::new(xs.len(), |i: int| 0);
        result
    }
}

fn is_ambiguous_permutation(xs: Vec<usize>) -> (result: bool)
    requires 
        xs.len() > 0,
        forall|i: int| 0 <= i < xs.len() ==> #[trigger] xs[i] >= 1 && #[trigger] xs[i] <= xs.len(),
        forall|i: int, j: int| 0 <= i < xs.len() && 0 <= j < xs.len() && i != j ==> #[trigger] xs[i] != #[trigger] xs[j],
    ensures 
        result <==> (xs@ == permutation_inverse(permutation_inverse(xs@))),
        result <==> (permutation_inverse(xs@) == xs@)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


}
fn main() {
    // let test1 = vec![1, 4, 3, 2];
    // let test2 = vec![2, 3, 4, 5, 1];
    // let test3 = vec![1];
    // println!("{}", is_ambiguous_permutation(test1));
    // println!("{}", is_ambiguous_permutation(test2));
    // println!("{}", is_ambiguous_permutation(test3));
}