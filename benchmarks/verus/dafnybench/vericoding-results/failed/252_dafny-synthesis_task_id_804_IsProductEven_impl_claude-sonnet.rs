use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_product_even(a: &[int]) -> (result: bool)
    ensures result <==> exists|i: int| 0 <= i < a.len() && is_even(a@[i])
// </vc-spec>
// <vc-code>
{
    for i in 0..a.len()
        invariant
            forall|j: int| 0 <= j < i ==> !is_even(a@[j])
    {
        if is_even(a[i]) {
            assert(0 <= i as int < a.len() && is_even(a@[i as int]));
            return true;
        }
    }
    
    assert(forall|i: int| 0 <= i < a.len() ==> !is_even(a@[i]));
    false
}
// </vc-code>

fn main() {
}

}