// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_remainder(a: nat, b: nat, c: nat) -> (result: nat)
    requires 
        a > 0,
        b < a,
        c > 0,
    ensures 
        result <= c,
        result % a == b,
        result + a > c || (result + a) % a != b,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // println!("{}", solve_remainder(7, 2, 10));
    // println!("{}", solve_remainder(5, 3, 12));
    // println!("{}", solve_remainder(10, 5, 100));
}