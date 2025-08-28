/* 
* Formal verification of O(n) and O(log n) algorithms to calculate the natural
* power of a real number (x^n), illustrating the usage of lemmas.
* FEUP, M.EIC, MFS, 2021/22.
*/

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{
    if n == 0 then 1.0 else x * power(x, n-1)
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).

// <vc-helpers>
lemma PowerIterInvariant(x: real, i: nat, n: nat, p: real)
    requires i <= n
    requires p == power(x, i)
    ensures p * power(x, n - i) == power(x, n)
    decreases n - i
{
    if i == n {
        assert power(x, n - i) == power(x, 0) == 1.0;
    } else {
        PowerIterInvariant(x, i + 1, n, p * x);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method powerIter(b: real, n: nat) returns (p : real)
    ensures p == power(b, n)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    p := 1.0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant p == power(b, i)
    {
        p := p * b;
        i := i + 1;
    }
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// A simple test case to make sure the specification is adequate.