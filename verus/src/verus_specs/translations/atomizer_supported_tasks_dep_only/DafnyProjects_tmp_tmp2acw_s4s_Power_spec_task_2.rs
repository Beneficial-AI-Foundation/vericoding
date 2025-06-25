use vstd::prelude::*;

verus! {

// Recursive definition of x^n in functional style, with time and space complexity O(n).
spec fn power(x: real, n: nat) -> real {
    if n == 0 { 1.0 } else { x * power(x, (n - 1) as nat) }
}

// Computation of x^n in time and space O(log n).
pub fn powerDC(x: real, n: nat) -> (p: real)
    ensures p == power(x, n)
{
}

proof fn productOfPowers(x: real, a: nat, b: nat)
    ensures power(x, a) * power(x, b) == power(x, a + b)
{
}

// A few test cases (checked statically by Dafny).
pub fn testPowerDC() {
}

}