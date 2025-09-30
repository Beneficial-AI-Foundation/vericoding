

// <vc-helpers>
function CommonDivisor(a: int, b: int, d: int): bool
    requires a > 0 && b > 0
{
    1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0
}

function SumOfCommonDivisorsUpTo(a: int, b: int, k: int): int
    requires a > 0 && b > 0
    requires 0 <= k <= a && k <= b
    ensures SumOfCommonDivisorsUpTo(a, b, k) >= 0
    decreases k
{
    if k == 0 then 0
    else if a % k == 0 && b % k == 0 then
        k + SumOfCommonDivisorsUpTo(a, b, k - 1)
    else
        SumOfCommonDivisorsUpTo(a, b, k - 1)
}

lemma SumContainsCommonDivisor(a: int, b: int, k: int, d: int)
    requires a > 0 && b > 0
    requires 0 <= k <= a && k <= b
    requires 1 <= d <= k
    requires a % d == 0 && b % d == 0
    ensures SumOfCommonDivisorsUpTo(a, b, k) >= d
    decreases k
{
    if k == d {
        assert a % k == 0 && b % k == 0;
        assert SumOfCommonDivisorsUpTo(a, b, k) == k + SumOfCommonDivisorsUpTo(a, b, k - 1);
        assert SumOfCommonDivisorsUpTo(a, b, k - 1) >= 0;
        assert SumOfCommonDivisorsUpTo(a, b, k) >= k;
    } else {
        SumContainsCommonDivisor(a, b, k - 1, d);
    }
}
// </vc-helpers>

// <vc-spec>
method SumOfCommonDivisors(a: int, b: int) returns (sum: int)
    requires a > 0 && b > 0
    ensures sum >= 0
    ensures forall d :: 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 ==> sum >= d
// </vc-spec>
// <vc-code>
{
    var minVal := if a <= b then a else b;
    sum := SumOfCommonDivisorsUpTo(a, b, minVal);
    
    forall d | 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0
        ensures sum >= d
    {
        if d <= minVal {
            SumContainsCommonDivisor(a, b, minVal, d);
        }
    }
}
// </vc-code>

