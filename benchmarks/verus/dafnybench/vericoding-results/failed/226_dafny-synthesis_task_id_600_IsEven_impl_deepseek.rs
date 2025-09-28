use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn is_even_proof(n: int)
    ensures
        n % 2 == 0 <==> exists|k: int| n == 2*k,
{
    assert(n % 2 == 0 ==> n == 2 * (n / 2)) by {
        assert(2 * (n / 2) + n % 2 == n);
    };
    assert(n == 2 * (n / 2) ==> n % 2 == 0) by {
        assert((2 * (n / 2)) % 2 == 0);
    };
}
// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures result <==> n % 2 == 0
// </vc-spec>
// <vc-code>
{
    proof {
        is_even_proof(n);
    }
    (n % 2) == 0
}
// </vc-code>

fn main() {
}

}