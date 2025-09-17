// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn gcd(a: int, b: int) -> int
    decreases (if b == 0 { 0 } else { (if b >= 0 { b } else { -b }) })
{
    if b == 0 {
        if a >= 0 { a } else { -a }
    } else {
        gcd(b, a % b)
    }
}

spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    a > 0 && b > 0 && c > 0 && d > 0
}

spec fn is_valid_fraction_string(s: Seq<char>, num: int, den: int) -> bool {
    num >= 0 && den > 0 && 
    gcd(num, den) == 1
    /* && s == int_to_string(num) + "/" + int_to_string(den) */
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int, c: int, d: int) -> (result: Seq<char>)
    requires valid_input(a, b, c, d)
    ensures ({
        let equal_case = a * d == b * c;
        let greater_case = a * d > b * c;
        let less_case = a * d < b * c;
        
        (equal_case ==> result == seq!['0', '/', '1']) &&
        (greater_case ==> exists|numerator: int, denominator: int| 
            numerator > 0 && denominator > 0 && 
            gcd(numerator, denominator) == 1 &&
            numerator * a * d == (a * d - b * c) * denominator) &&
        (less_case ==> exists|numerator: int, denominator: int| 
            numerator > 0 && denominator > 0 && 
            gcd(numerator, denominator) == 1 &&
            numerator * b * c == (b * c - a * d) * denominator)
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}