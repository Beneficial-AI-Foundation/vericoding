use vstd::prelude::*;

verus! {

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
spec fn power(x: real, n: nat) -> real
{
    if n == 0 { 1.0 } else { x * power(x, (n-1) as nat) }
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).
pub fn powerIter(x: real, n: nat) -> (p: real)
    ensures p == power(x, n)
{
}

proof fn distributiveProperty(x: real, a: nat, b: nat) 
    ensures power(x, a) * power(x, b) == power(x, (a + b) as nat)
{
}

// A simple test case to make sure the specification is adequate.
pub fn testPowerIter()
{
}

}