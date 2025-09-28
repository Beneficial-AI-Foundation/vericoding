use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn is_product_even(a: &[int]) -> (result: bool)
    ensures result <==> exists|i: int| 0 <= i < a.len() && is_even(a@[i])
// </vc-spec>
// <vc-code>
{
    let n: int = a.len() as int;
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant forall |j: int| 0 <= j && j < i ==> !is_even(a@[j]);
        decreases n - i
    {
        if is_even(a@[i]) {
            proof {
                assert(0 <= i && i < n);
                assert(is_even(a@[i]));
                assert(exists|j: int| 0 <= j && j < n && is_even(a@[j]));
            }
            return true;
        }
        i = i + 1;
    }

    proof {
        // From the loop invariants and loop exit condition we get that no element is even.
        assert(i >= n);
        assert(i <= n);
        assert(i == n);
        assert(forall |j: int| 0 <= j && j < n ==> !is_even(a@[j]));
        assert(!exists|j: int| 0 <= j && j < n && is_even(a@[j]));
    }
    return false;
}
// </vc-code>

fn main() {
}

}