use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn is_armstrong(n: int) -> (result: bool)
    requires 100 <= n < 1000
    ensures result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
// </vc-spec>
// <vc-code>
{
    n == ((n / 100) * (n / 100) * (n / 100)
        + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10)
        + (n % 10) * (n % 10) * (n % 10))
}
// </vc-code>

fn main() {
}

}