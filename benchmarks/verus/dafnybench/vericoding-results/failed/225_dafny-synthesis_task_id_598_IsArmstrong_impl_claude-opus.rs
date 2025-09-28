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
    let hundreds = n / 100;
    let tens = (n / 10) % 10;
    let ones = n % 10;
    
    let sum = hundreds * hundreds * hundreds + tens * tens * tens + ones * ones * ones;
    
    sum == n
}
// </vc-code>

fn main() {
}

}