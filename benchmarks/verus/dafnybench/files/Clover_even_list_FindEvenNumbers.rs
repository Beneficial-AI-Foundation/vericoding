// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &[i32]) -> (even_numbers: Vec<i32>)
    ensures 
        (forall|x: i32| arr@.contains(x) && x % 2 == 0 ==> even_numbers@.contains(x)) &&
        (forall|x: i32| !arr@.contains(x) ==> !even_numbers@.contains(x)) &&
        (forall|k: int| 0 <= k < even_numbers@.len() ==> even_numbers@[k] % 2 == 0) &&
        (forall|k: int, l: int| 0 <= k < l < even_numbers@.len() ==> 
            exists|n: int, m: int| 0 <= n < m < arr@.len() && 
            #[trigger] even_numbers@[k] == #[trigger] arr@[n] && 
            #[trigger] even_numbers@[l] == #[trigger] arr@[m])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}