predicate ValidInput(n: int)
{
    n >= 1
}

predicate DivisibleByBoth(result: int, n: int)
    requires n >= 1
{
    result % 2 == 0 && result % n == 0
}

predicate IsSmallest(result: int, n: int)
    requires n >= 1
{
    forall k: int :: 1 <= k < result ==> !(k % 2 == 0 && k % n == 0)
}

function LCM(a: int, b: int): int
    requires a >= 1 && b >= 1
{
    if a % b == 0 then a
    else if b % a == 0 then b
    else a * b
}

// <vc-helpers>
lemma LCMProperties(a: int, b: int)
    requires a >= 1 && b >= 1
    ensures LCM(a, b) >= 1
    ensures LCM(a, b) % a == 0
    ensures LCM(a, b) % b == 0
    ensures forall k: int :: 1 <= k < LCM(a, b) ==> !(k % a == 0 && k % b == 0)
{
    if a % b == 0 {
        // LCM(a, b) == a
    } else if b % a == 0 {
        // LCM(a, b) == b  
    } else {
        // LCM(a, b) == a * b
    }
}

lemma EvenCase(n: int)
    requires n >= 1 && n % 2 == 0
    ensures DivisibleByBoth(n, n)
    ensures IsSmallest(n, n)
{
    assert n % 2 == 0 && n % n == 0;
    forall k: int | 1 <= k < n
        ensures !(k % 2 == 0 && k % n == 0)
    {
        if k % 2 == 0 && k % n == 0 {
            assert k >= n;
            assert false;
        }
    }
}

lemma OddCase(n: int)
    requires n >= 1 && n % 2 != 0
    ensures DivisibleByBoth(n * 2, n)
    ensures IsSmallest(n * 2, n)
{
    assert (n * 2) % 2 == 0 && (n * 2) % n == 0;
    forall k: int | 1 <= k < n * 2
        ensures !(k % 2 == 0 && k % n == 0)
    {
        if k % 2 == 0 && k % n == 0 {
            if k == n {
                assert n % 2 == 0;
                assert false;
            } else {
                assert k >= n * 2;
                assert false;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 1
    ensures DivisibleByBoth(result, n)
    ensures IsSmallest(result, n)
    ensures (n % 2 == 0 ==> result == n) && (n % 2 != 0 ==> result == n * 2)
// </vc-spec>
// <vc-code>
{
    if n % 2 == 0 {
        result := n;
        EvenCase(n);
    } else {
        result := n * 2;
        OddCase(n);
    }
}
// </vc-code>

