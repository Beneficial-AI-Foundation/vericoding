// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &[int]) -> (even_numbers: Vec<int>)
    ensures

        forall|i: int| 0 <= i < arr.len() && is_even(arr[i]) ==> 
            #[trigger] even_numbers@.contains(arr[i]),

        forall|x: int| #[trigger] even_numbers@.contains(x) ==> 
            exists|i: int| 0 <= i < arr.len() && arr[i] == x,

        forall|k: int, l: int| 0 <= k < l < even_numbers.len() ==>
            exists|n: int, m: int| 0 <= n < m < arr.len() && 
                #[trigger] even_numbers[k] == arr[n] && 
                #[trigger] even_numbers[l] == arr[m]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}