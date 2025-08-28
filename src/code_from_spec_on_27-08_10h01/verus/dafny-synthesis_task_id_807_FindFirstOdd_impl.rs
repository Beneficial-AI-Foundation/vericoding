use vstd::prelude::*;

verus! {

spec fn is_odd(x: int) -> bool {
    x % 2 != 0
}

// <vc-helpers>
spec fn spec_index(a: &[i32], i: int) -> int {
    a[i as usize] as int
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find_first_odd(a: &[i32]) -> (result: (bool, usize))
    ensures 
        (!result.0 ==> (forall|i: int| 0 <= i < a.len() ==> !is_odd(a[i] as int))) &&
        (result.0 ==> (0 <= result.1 < a.len() && 
                      is_odd(a[result.1 as int] as int) && 
                      (forall|i: int| 0 <= i < result.1 ==> !is_odd(a[i] as int))))
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> !is_odd(spec_index(a, j))
    {
        let val = a[i];
        if val % 2 != 0 {
            proof {
                assert(is_odd(spec_index(a, i as int)));
            }
            return (true, i);
        }
        i += 1;
    }
    (false, 0)
}
// </vc-code>

fn main() {}

}