use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn is_product_even(a: &[int]) -> (result: bool)
    ensures result <==> exists|i: int| 0 <= i < a.len() && is_even(a@[i])
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> !is_even(a@[j]),
    {
        if a[i] % 2 == 0 {
            assert(is_even(a@[i as int]));
            assert(0 <= i < a.len());
            return true;
        }
        i = i + 1;
    }
    
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> !is_even(a@[j]));
    false
}
// </vc-code>

fn main() {
}

}