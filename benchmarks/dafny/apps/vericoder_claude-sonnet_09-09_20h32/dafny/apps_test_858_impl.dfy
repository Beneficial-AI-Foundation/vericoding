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
    requires n >= 1
    ensures exists z :: 1 <= z <= n && IsPowerOfTwo(z)
{
    assert IsPowerOfTwo(1);
}

lemma PowerOfTwoMonotonic(a: int, b: int)
    requires IsPowerOfTwo(a) && IsPowerOfTwo(b) && a < b
    ensures a * 2 <= b
    decreases b
{
    if b == 1 {
        assert false;
    } else {
        assert b % 2 == 0;
        var b_half := b / 2;
        assert IsPowerOfTwo(b_half);
        if a < b_half {
            PowerOfTwoMonotonic(a, b_half);
            assert a * 2 <= b_half;
            assert a * 2 * 2 <= b_half * 2;
            assert a * 4 <= b;
        } else if a == b_half {
            assert a * 2 == b;
        } else {
            assert false;
        }
    }
}

function FindLargestPowerOfTwo(n: int, candidate: int): int
    requires n >= 1 && candidate >= 1 && IsPowerOfTwo(candidate) && candidate <= n
    ensures IsPowerOfTwo(FindLargestPowerOfTwo(n, candidate))
    ensures candidate <= FindLargestPowerOfTwo(n, candidate) <= n
    ensures FindLargestPowerOfTwo(n, candidate) * 2 > n
    decreases n - candidate
{
    if candidate * 2 <= n then
        FindLargestPowerOfTwo(n, candidate * 2)
    else
        candidate
}

lemma FindLargestPowerOfTwoCorrect(n: int, candidate: int)
    requires n >= 1 && candidate >= 1 && IsPowerOfTwo(candidate) && candidate <= n
    ensures var z := FindLargestPowerOfTwo(n, candidate);
            IsPowerOfTwo(z) && z <= n && z * 2 > n
{
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
        var z := FindLargestPowerOfTwo(n, 1);
        FindLargestPowerOfTwoCorrect(n, 1);
        result := (n - z) / 2;
    }
}
// </vc-code>

