// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &[i8]) -> (even_numbers: Vec<i8>)
    ensures 
        (forall|x: i8| #[trigger] arr@.contains(x) && x as int % 2 == 0 ==> #[trigger] even_numbers@.contains(x)) &&
        (forall|x: i8| !arr@.contains(x) ==> !even_numbers@.contains(x)) &&
        (forall|k: int| 0 <= k < even_numbers@.len() ==> even_numbers@[k] as int % 2 == 0) &&
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