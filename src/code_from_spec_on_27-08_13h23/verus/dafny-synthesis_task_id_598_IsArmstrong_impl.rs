use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_armstrong(n: int) -> (result: bool)
    requires 100 <= n < 1000
    ensures result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
// </vc-spec>
// </vc-spec>

// <vc-code>
fn is_armstrong(n: int) -> (result: bool)
    requires 100 <= n < 1000
    ensures result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
{
    let hundreds = n / 100;
    let tens = (n / 10) % 10;
    let ones = n % 10;
    let sum_of_cubes = hundreds * hundreds * hundreds + tens * tens * tens + ones * ones * ones;
    n == sum_of_cubes
}
// </vc-code>

fn main() {
}

}