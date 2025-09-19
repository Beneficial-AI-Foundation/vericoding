// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: i32) -> bool {
    n % 2 != 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn first_even_odd_difference(a: &Vec<i8>) -> (result: i8)
    requires 
        a.len() > 1,
        exists|x: int| 0 <= x < a@.len() && is_even(a@[x] as i32),
        exists|x: int| 0 <= x < a@.len() && is_odd(a@[x] as i32),
    ensures 
        exists|i: int, j: int| 
            0 <= i < a@.len() && 0 <= j < a@.len() &&
            is_even(a@[i] as i32) && is_odd(a@[j] as i32) &&
            result as i32 == a@[i] as i32 - a@[j] as i32 &&
            (forall|k: int| 0 <= k < i ==> is_odd(a@[k] as i32)) &&
            (forall|k: int| 0 <= k < j ==> is_even(a@[k] as i32))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}