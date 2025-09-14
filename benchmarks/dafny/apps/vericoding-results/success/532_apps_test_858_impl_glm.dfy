predicate IsPowerOfTwo(n: int) 
    decreases n
{
    if n <= 0 then false
    else if n == 1 then true
    else if n % 2 == 1 then false
    else IsPowerOfTwo(n / 2)
}

predicate ValidInput(n: int) {
    n >= 1
}

predicate CorrectResult(n: int, result: int) {
    if n % 2 == 1 then 
        result == (n - 1) / 2
    else 
        exists z :: 1 <= z <= n && IsPowerOfTwo(z) && z <= n && z * 2 > n && result == (n - z) / 2
}

// <vc-helpers>
lemma {:opaque} IsPowerOfTwoMultiply(n: int)
    requires IsPowerOfTwo(n)
    ensures IsPowerOfTwo(n * 2)
{
    reveal IsPowerOfTwo();
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures CorrectResult(n, result)
// </vc-spec>
// <vc-code>
{
    if n % 2 == 1 {
        return (n-1)/2;
    } else {
        var z := 1;
        while z * 2 <= n
            invariant 1 <= z
            invariant z <= n
            invariant IsPowerOfTwo(z)
            decreases n - z
        {
            z := z * 2;
            IsPowerOfTwoMultiply(z / 2);
        }
        assert z * 2 > n;
        return (n - z) / 2;
    }
}
// </vc-code>

