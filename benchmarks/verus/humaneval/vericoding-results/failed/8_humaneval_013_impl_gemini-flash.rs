// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> nat {
    if x >= 0 { x as nat } else { (-x) as nat }
}

spec fn divides(d: int, n: int) -> bool {
    if d == 0 { n == 0 } else { n % d == 0 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes to fixed helper. */
fn euclidean_gcd_nat(a: nat, b: nat) -> (result: nat)
    ensures
        (a == 0 && b == 0) ==> result == 0,
        (a != 0 || b != 0) ==> result > 0,
        divides(result as int, a as int) && divides(result as int, b as int),
        forall|d: int| d > 0 && divides(d, a as int) && divides(d, b as int) ==> d <= result as int
{
    let mut x: nat = a;
    let mut y: nat = b;

    while y != 0
        invariant
            y >= 0,
            x >= 0,
            forall|d: int| d > 0 && divides(d, a as int) && divides(d, b as int) <==> (divides(d, x as int) && divides(d, y as int)),
        decreases y
    {
        let temp_x = x;
        x = y;
        y = temp_x % y;
    }
    x
}
// </vc-helpers>

// <vc-spec>
fn greatest_common_divisor(a: i8, b: i8) -> (result: u8)
    ensures 
        result > 0 <==> (a != 0 || b != 0),
        result == 0 <==> (a == 0 && b == 0),
        divides(result as int, a as int) && divides(result as int, b as int),
        forall|d: int| d > 0 && divides(d, a as int) && divides(d, b as int) ==> d <= result as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type errors by removing explicit `as int` casts for `int` type, which caused compilation errors. Managed the conversion to `nat` using `abs` for calculating GCD. */
{
    if a == 0 && b == 0 {
        return 0; // result = 0 if a = 0 and b = 0
    }

    let a_val: int = a as int;
    let b_val: int = b as int;

    let a_nat = abs(a_val);
    let b_nat = abs(b_val);

    let gcd_result_nat = euclidean_gcd_nat(a_nat, b_nat);
    
    // The result from euclidean_gcd_nat is `nat`. We need to cast it to `u8`.
    // Since we handled the (0,0) case, we know gcd_result_nat is > 0 and fits in u8
    gcd_result_nat as u8
}
// </vc-code>


}

fn main() {}