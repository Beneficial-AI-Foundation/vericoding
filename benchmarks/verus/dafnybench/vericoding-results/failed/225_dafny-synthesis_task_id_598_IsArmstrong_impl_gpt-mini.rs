use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no changes required)
// </vc-helpers>

// <vc-spec>
fn is_armstrong(n: int) -> (result: bool)
    requires 100 <= n < 1000
    ensures result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
// </vc-spec>
// <vc-code>
{
    let a: int = n / 100.into();
    let b: int = (n / 10.into()) % 10.into();
    let c: int = n % 10.into();
    a * a * a + b * b * b + c * c * c == n
}
// </vc-code>

fn main() {
}

}