use vstd::prelude::*;

verus! {

spec fn is_odd(x: int) -> bool {
    x % 2 != 0
}

// <vc-helpers>
// Helpers: no additional helpers required for this proof.
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
        invariant i <= a.len() &&
                  (forall|k: int| 0 <= k < i as int ==> !is_odd(a@[k] as int))
        decreases a.len() - i
    {
        if a[i] % 2 != 0 {
            proof {
                assert(i < a.len());
                assert(is_odd(a@[i as int] as int));
                assert(forall|k: int| 0 <= k < i as int ==> !is_odd(a@[k] as int));
            }
            return (true, i);
        }
        proof {
            assert(!is_odd(a@[i as int] as int));
        }
        i += 1;
    }
    proof {
        // From loop exit and invariant we get i == a.len()
        assert(!(i < a.len()));
        assert(i <= a.len());
        assert(i >= a.len());
        assert(i == a.len());
        // Use invariant to conclude all elements are not odd
        assert(forall|k: int| 0 <= k < i as int ==> !is_odd(a@[k] as int));
        assert(forall|k: int| 0 <= k < a.len() as int ==> !is_odd(a@[k] as int));
    }
    return (false, 0);
}
// </vc-code>

fn main() {}

}