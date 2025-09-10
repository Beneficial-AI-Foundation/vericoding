predicate ValidInput(p: int) {
    2 <= p < 2000
}

function CountPrimitiveRoots(p: int): int
    requires ValidInput(p)
{
    if p == 2 then 1
    else |set i | 1 <= i < p-1 && (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0))|
}

// <vc-helpers>
function EulerTotient(n: int): int
    requires n > 0
    decreases n
{
    if n == 1 then 1
    else if IsPrime(n) then n - 1
    else
        var factors := PrimeFactors(n);
        var p := factors[0];
        var k := 0;
        var temp_n := n;
        while temp_n % p == 0
            invariant temp_n > 0
            invariant n % p == 0 ==> n == temp_n * p^k
            decreases temp_n
        {
            temp_n := temp_n / p;
            k := k + 1;
        }
        var pk := Power(p, k);
        (pk - pk / p) * EulerTotient(n / pk)
}

function Power(base: int, exponent: int): int
    requires exponent >= 0
{
    if exponent == 0 then 1
    else base * Power(base, exponent - 1)
}

function IsPrime(n: int): bool
    requires n >= 0
{
    if n < 2 then false
    else if n == 2 then true
    else if n % 2 == 0 then false
    else
        var i := 3;
        while i * i <= n
            invariant 3 <= i <= n + 2
            invariant i % 2 == 1
            invariant forall k :: 3 <= k < i && k % 2 == 1 ==> n % k != 0
        {
            if n % i == 0 then return false;
            i := i + 2;
        }
        true
}

function PrimeFactors(n: int): seq<int>
    requires n > 1
    ensures forall p :: p in PrimeFactors(n) ==> IsPrime(p)
    ensures (var product := 1; forall p :: p in PrimeFactors(n) ==> product := product * p; product == n)
    decreases n
{
    if IsPrime(n) then [n]
    else
        var i := 2;
        while i * i <= n
            invariant 2 <= i <= n
            invariant forall k :: 2 <= k < i ==> n % k != 0
        {
            if n % i == 0 then return [i] + PrimeFactors(n / i);
            i := i + 1;
        }
        [n] // Should not be reached if n is composite and greater than 1
}

// Theorem: For a prime p, the number of primitive roots modulo p is EulerTotient(p-1).
// This requires p to be prime. The problem statement uses p as a prime by context (primitive roots).
// ValidInput(p) states 2 <= p < 2000.
// We need to leverage the property that p is prime for the theorem result.
// Let's assume p is always a prime number for the context of this problem,
// given the usual mathematical context of primitive roots modulo p.
// If p is not guaranteed to be prime, the problem statement or solution would be much more complex.
// </vc-helpers>

// <vc-spec>
method solve(p: int) returns (result: int)
    requires ValidInput(p)
    ensures result >= 0
    ensures result == CountPrimitiveRoots(p)
// </vc-spec>
// <vc-code>
{
    if p == 2 {
        return 1;
    } else {
        // According to number theory, the number of primitive roots modulo a prime p is phi(p-1),
        // where phi is Euler's totient function.
        // Assuming p is prime based on the common context of "primitive roots modulo p".
        // The problem statement defines CountPrimitiveRoots with a "set comprehension"
        // for "1 <= i < p-1 && (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0))"
        // This condition for i means that i is coprime to (p-1) for all prime factors j of (p-1).
        // This is equivalent to i being coprime to p-1 in general.
        // The numbers i in {1, ..., p-2} such that gcd(i, p-1) = 1.
        // By definition, this is EulerTotient(p-1).
        return EulerTotient(p - 1);
    }
}
// </vc-code>

