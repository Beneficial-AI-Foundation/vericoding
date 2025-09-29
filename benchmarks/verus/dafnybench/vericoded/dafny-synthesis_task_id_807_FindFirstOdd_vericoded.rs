use vstd::prelude::*;

verus! {

spec fn is_odd(x: int) -> bool {
    x % 2 != 0
}

// <vc-helpers>
// no helper updates needed
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
            i <= a.len(),
            forall|j: int| 0 <= j && j < i as int ==> !is_odd(a[j] as int)
        decreases a.len() - i
    {
        if a[i] % 2 != 0 {
            assert(is_odd(a[i as int] as int));
            return (true, i);
        } else {
            assert(!is_odd(a[i as int] as int));
        }
        i += 1;
    }
    assert(!(i < a.len()));
    assert(i >= a.len());
    assert(i <= a.len());
    assert(i == a.len());
    assert(forall|j: int| 0 <= j && j < a.len() as int ==> !is_odd(a[j] as int));
    (false, 0)
}
// </vc-code>

fn main() {}

}