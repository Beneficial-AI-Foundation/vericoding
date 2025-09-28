// <vc-preamble>
predicate ValidInput(p: int) {
    2 <= p < 2000
}

function CountPrimitiveRoots(p: int): int
    requires ValidInput(p)
{
    if p == 2 then 1
    else |set i | 1 <= i < p-1 && (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0))|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected Gcd function signature and implementation. */
function Totient_phi(n: int): int
    requires n >= 1
    ensures Totient_phi(n) >= 1
{
    if n == 1 then 1
    else |set k | 1 <= k < n && Gcd(k, n) == 1|
}

function Gcd(a: int, b: int): int
    requires a >= 0 && b >= 0
    ensures Gcd(a, b) >= 0
    ensures (a == 0 && b == 0) ==> Gcd(a, b) == 0
    ensures (a == 0 && b != 0) ==> Gcd(a, b) == b
    ensures (a != 0 && b == 0) ==> Gcd(a, b) == a
    decreases a, b
{
    if a == 0 then b
    else if b == 0 then a
    else if a > b then Gcd(a % b, b)
    else Gcd(a, b % a)
}

// </vc-helpers>

// <vc-spec>
method solve(p: int) returns (result: int)
    requires ValidInput(p)
    ensures result >= 0
    ensures result == CountPrimitiveRoots(p)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): This implementation directly calls the Totient_phi helper function, which correctly calculates the number of primitive roots for a prime `p`. The `if (p == 2)` condition is handled as a special case, and for other primes, `Totient_phi(p - 1)` provides the result as per number theory. */
{
    if p == 2 {
        result := 1;
    } else {
        result := Totient_phi(p - 1);
    }
}
// </vc-code>
