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
    
    let hundreds_cubed = hundreds * hundreds * hundreds;
    let tens_cubed = tens * tens * tens;
    let ones_cubed = ones * ones * ones;
    
    let sum = hundreds_cubed + tens_cubed + ones_cubed;
    
    n == sum
}
// </vc-code>

fn main() {
}

}