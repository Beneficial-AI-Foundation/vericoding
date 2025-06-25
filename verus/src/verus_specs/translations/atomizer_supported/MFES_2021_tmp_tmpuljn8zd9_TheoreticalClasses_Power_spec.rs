// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
// ATOM 

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
spec fn power(x: real, n: nat) -> real
{
    if n == 0 { 1.0 } else { x * power(x, (n-1) as nat) }
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).
// SPEC 

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).
pub fn powerIter(x: real, n: nat) -> (p: real)
    ensures(p == power(x, n))
{
}

// Recursive version, imperative, with time and space complexity O(log n).
// SPEC 

// Recursive version, imperative, with time and space complexity O(log n).
pub fn powerOpt(x: real, n: nat) -> (p: real)
    ensures(p == power(x, n))
{
}

// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of. 
proof fn distributiveProperty(x: real, a: nat, b: nat) 
    ensures(power(x, a) * power(x, b) == power(x, a + b))
{
}

// A simple test case to make sure the specification is adequate.
// SPEC 

// A simple test case to make sure the specification is adequate.
pub fn testPowerIter()
{
}

// SPEC 

pub fn testPowerOpt()
{
}