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
lemma PowerOfTwoExists(n: int)
    requires n >= 2 && n % 2 == 0
    ensures exists z :: 1 <= z <= n && IsPowerOfTwo(z) && z <= n && z * 2 > n
{
    var z := 1;
    while z * 2 <= n
        invariant 1 <= z <= n
        invariant IsPowerOfTwo(z)
        invariant z <= n
    {
        z := z * 2;
        assert IsPowerOfTwo(z);
    }
    assert z * 2 > n;
    assert 1 <= z <= n && IsPowerOfTwo(z) && z <= n && z * 2 > n;
}

lemma PowerOfTwoDoubling(z: int)
    requires z >= 1
    requires IsPowerOfTwo(z)
    ensures IsPowerOfTwo(2 * z)
{
    // This follows from the definition of IsPowerOfTwo
    assert (2 * z) % 2 == 0;
    assert (2 * z) / 2 == z;
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
        result := (n - 1) / 2;
    } else {
        var z := 1;
        while z * 2 <= n
            invariant 1 <= z <= n
            invariant IsPowerOfTwo(z)
            invariant z <= n
        {
            PowerOfTwoDoubling(z);
            z := z * 2;
        }
        result := (n - z) / 2;
    }
}
// </vc-code>

