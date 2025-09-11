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
fn find_even_numbers(arr: &[i32]) -> (even_list: Vec<i32>)

    ensures 
        forall|i: int| 0 <= i < even_list.len() ==> is_even(even_list[i] as int) && exists|j: int| 0 <= j < arr.len() && arr[j] == even_list[i],

        forall|i: int| 0 <= i < arr.len() && is_even(arr[i] as int) ==> exists|j: int| 0 <= j < even_list.len() && even_list[j] == arr[i]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}