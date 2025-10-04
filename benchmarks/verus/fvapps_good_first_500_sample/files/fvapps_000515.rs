// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn parse_fraction_parts(result: String) -> (u32, u32);

spec fn gcd_spec(a: u32, b: u32) -> u32;

fn calc_gcd_prob(n: u32) -> (result: String)
    requires n > 0 && n <= 1000,
    ensures 
        parse_fraction_parts(result).1 > 0,
        gcd_spec(parse_fraction_parts(result).0, parse_fraction_parts(result).1) == 1,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>

/* Apps difficulty: interview */
/* Assurance level: unguarded */

fn main() {
    // println!("{}", calc_gcd_prob(1)); // Should output "1/1"
    // println!("{}", calc_gcd_prob(2)); // Should output "3/4"
    // println!("{}", calc_gcd_prob(3)); // Should output "5/9"
}

}