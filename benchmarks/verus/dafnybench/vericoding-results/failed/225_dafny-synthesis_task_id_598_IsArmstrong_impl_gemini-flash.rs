use vstd::prelude::*;

verus! {

// <vc-helpers>
#[macro_export]
macro_rules! pow3 {
    ($b:expr) => {
        $b * $b * $b
    };
}

#[inline]
pub fn pow3_int(b: int) -> int {
    b * b * b
}
// </vc-helpers>

// <vc-spec>
fn is_armstrong(n: int) -> (result: bool)
    requires 100 <= n < 1000
    ensures result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
// </vc-spec>
// <vc-code>
{
    let mut n_hundreds: int = 0;
    let mut n_tens: int = 0;
    let mut n_units: int = 0;

    // Calculate hundreds digit
    n_hundreds = n / 100;

    // Calculate tens digit
    n_tens = (n / 10) % 10;

    // Calculate units digit
    n_units = n % 10;

    // Calculate the sum of the cubes of the digits
    let sum_cubes = pow3_int(n_hundreds) + pow3_int(n_tens) + pow3_int(n_units);

    // Check if n is equal to the sum of the cubes of its digits
    let result = n == sum_cubes;

    result
}
// </vc-code>

fn main() {
}

}