use vstd::prelude::*;

verus! {

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
pub open spec fn power(x: real, n: nat) -> real
{
    if n == 0 { 1.0 } else { x * power(x, (n-1) as nat) }
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).
pub fn powerIter(x: real, n: nat) -> (p: real)
    ensures p == power(x, n)
{
    todo!()
}

// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of.
proof fn distributiveProperty(x: real, a: nat, b: nat)
    ensures power(x, a) * power(x, b) == power(x, a + b)
{
    todo!()
}

}