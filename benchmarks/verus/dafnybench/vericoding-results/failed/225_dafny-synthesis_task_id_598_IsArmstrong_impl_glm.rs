use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_armstrong(n: int) -> (result: bool)
    requires 100 <= n < 1000
    ensures result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
// </vc-spec>
// <vc-code>
{
    let d1 = n / 100;
    let d2 = (n / 10) % 10;
    let d3 = n % 10;
    let sum = d1 * d1 * d1 + d2 * d2 * d2 + d3 * d3 * d3;
    n == sum
}
// </vc-code>

fn main() {
}

}