// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_odd(x: int) -> bool {
    x % 2 != 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_first_odd(a: &[i32]) -> (result: (bool, usize))
    ensures 
        (!result.0 ==> (forall|i: int| 0 <= i < a.len() ==> !is_odd(a[i] as int))) &&
        (result.0 ==> (0 <= result.1 < a.len() && 
                      is_odd(a[result.1 as int] as int) && 
                      (forall|i: int| 0 <= i < result.1 ==> !is_odd(a[i] as int))))
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> !is_odd(a[j] as int),
        decreases a.len() - i
    {
        if a[i] % 2 != 0 {
            return (true, i);
        }
        i = i + 1;
    }
    (false, 0)
}
// </vc-code>

}
fn main() {}