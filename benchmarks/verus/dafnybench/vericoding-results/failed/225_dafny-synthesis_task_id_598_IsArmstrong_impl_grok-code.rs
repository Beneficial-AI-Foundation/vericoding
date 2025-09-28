use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_armstrong(n: int) -> (result: bool)
    requires 100 <= n < 1000
    ensures result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
// </vc-spec>
// <vc-code>
{
    let a = n / (100 as int);
    let b = (n / (10 as int)) % (10 as int);
    let c = n % (10 as int);
    assert(1 <= a && a <= 9);
    assert(0 <= b && b < 10);
    assert(0 <= c && c < 10);
    let cube_a = a * a * a;
    let cube_b = b * b * b;
    let cube_c = c * c * c;
    let sum = cube_a + cube_b + cube_c;
    assert(sum == a * a * a + b * b * b + c * c * c);
    sum == n
}
// </vc-code>

fn main() {
}

}