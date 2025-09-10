predicate ValidInput(n: int, k: int)
{
    n >= 1 && k >= 1
}

predicate AllRemaindersDistinct(n: int, k: int)
    requires ValidInput(n, k)
{
    forall i :: 1 <= i <= k ==> n % i == (i - 1)
}

predicate HasNonDistinctRemainder(n: int, k: int)
    requires ValidInput(n, k)
{
    exists i :: 1 <= i <= k && n % i != (i - 1)
}

// <vc-helpers>
lemma RemainderLemma(n: int, k: int, i: int)
    requires ValidInput(n, k)
    requires 1 <= i <= k
    ensures n % i == i - 1 <==> (n + 1) % i == 0
{
    // (n + 1) % i == 0 if and only if n % i == i - 1
    // This follows from the property: (a + b) % m = (a % m + b % m) % m
    // So (n + 1) % i = (n % i + 1) % i
    // If n % i == i - 1, then (i - 1 + 1) % i = i % i = 0
    // If (n + 1) % i == 0, then n % i must be i - 1
}

lemma LCMProperty(n: int, k: int)
    requires ValidInput(n, k)
    ensures AllRemaindersDistinct(n, k) <==> (n + 1) % i != 0 for all i in 2..k
{
    // The condition n % i == i - 1 for all i in 1..k is equivalent to
    // (n + 1) being divisible by all i in 1..k, which means
    // (n + 1) must be a multiple of the LCM of numbers 1 through k
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: string)
    requires ValidInput(n, k)
    ensures result == "Yes\n" <==> AllRemaindersDistinct(n, k)
    ensures result == "No\n" <==> HasNonDistinctRemainder(n, k)
// </vc-spec>
// <vc-code>
{
    var lcm := 1;
    var i := 1;
    
    while i <= k
        invariant 1 <= i <= k + 1
        invariant lcm > 0
        invariant forall j :: 1 <= j < i ==> lcm % j == 0
    {
        var gcd_val := GCD(lcm, i);
        lcm := lcm * i / gcd_val;
        i := i + 1;
    }
    
    if (n + 1) % lcm == 0 {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}

function GCD(a: nat, b: nat): nat
    requires a > 0 || b > 0
    decreases a + b
{
    if b == 0 then
        a
    else
        GCD(b, a % b)
}
// </vc-code>

