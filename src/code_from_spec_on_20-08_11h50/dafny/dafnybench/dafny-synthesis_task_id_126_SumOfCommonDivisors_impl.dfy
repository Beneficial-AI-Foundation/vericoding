function gcd(a: int, b: int): int
    requires a > 0 && b > 0
    decreases a + b
{
    if a == b then a
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
}

function sumDivisors(n: int, limit: int): int
    requires n > 0 && limit >= 0
    decreases limit
{
    if limit == 0 then 0
    else if n % limit == 0 then limit + sumDivisors(n, limit - 1)
    else sumDivisors(n, limit - 1)
}

function sumCommonDivisorsUpTo(a: int, b: int, limit: int): int
    requires a > 0 && b > 0 && limit >= 0
    decreases limit
{
    if limit == 0 then 0
    else if a % limit == 0 && b % limit == 0 then limit + sumCommonDivisorsUpTo(a, b, limit - 1)
    else sumCommonDivisorsUpTo(a, b, limit - 1)
}

// <vc-helpers>
lemma CommonDivisorBound(a: int, b: int, d: int)
    requires a > 0 && b > 0
    requires d > 0 && a % d == 0 && b % d == 0
    ensures d <= a && d <= b
{
    // A divisor of a positive number cannot exceed that number
}

lemma SumCommonDivisorsNonNegative(a: int, b: int, limit: int)
    requires a > 0 && b > 0 && limit >= 0
    ensures sumCommonDivisorsUpTo(a, b, limit) >= 0
    decreases limit
{
    if limit == 0 {
        // Base case: sumCommonDivisorsUpTo(a, b, 0) = 0 >= 0
    } else if a % limit == 0 && b % limit == 0 {
        // Recursive case: sumCommonDivisorsUpTo(a, b, limit) = limit + sumCommonDivisorsUpTo(a, b, limit - 1)
        SumCommonDivisorsNonNegative(a, b, limit - 1);
        assert sumCommonDivisorsUpTo(a, b, limit - 1) >= 0;
        assert limit > 0;
        assert sumCommonDivisorsUpTo(a, b, limit) == limit + sumCommonDivisorsUpTo(a, b, limit - 1);
        assert sumCommonDivisorsUpTo(a, b, limit) >= limit >= 0;
    } else {
        // Recursive case: sumCommonDivisorsUpTo(a, b, limit) = sumCommonDivisorsUpTo(a, b, limit - 1)
        SumCommonDivisorsNonNegative(a, b, limit - 1);
    }
}

lemma SumIncludesAllCommonDivisors(a: int, b: int, limit: int, d: int)
    requires a > 0 && b > 0 && limit >= 0
    requires 1 <= d <= limit && a % d == 0 && b % d == 0
    ensures sumCommonDivisorsUpTo(a, b, limit) >= d
    decreases limit
{
    if limit == 0 {
        // Contradiction since d >= 1 > 0 = limit
        assert false;
    } else if a % limit == 0 && b % limit == 0 {
        if d == limit {
            // d is included in this step - sumCommonDivisorsUpTo(a, b, limit) = limit + sumCommonDivisorsUpTo(a, b, limit - 1) >= limit = d
            assert sumCommonDivisorsUpTo(a, b, limit) == limit + sumCommonDivisorsUpTo(a, b, limit - 1);
            SumCommonDivisorsNonNegative(a, b, limit - 1);
            assert sumCommonDivisorsUpTo(a, b, limit) >= limit;
            assert limit == d;
        } else {
            // d < limit, so it's included in the recursive call
            SumIncludesAllCommonDivisors(a, b, limit - 1, d);
        }
    } else {
        // limit is not a common divisor, so d < limit
        assert d < limit;
        SumIncludesAllCommonDivisors(a, b, limit - 1, d);
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
    var limit := if a <= b then a else b;
    sum := 0;
    var i := 1;
    
    while i <= limit
        invariant 0 <= i <= limit + 1
        invariant sum >= 0
        invariant forall d :: 1 <= d < i && a % d == 0 && b % d == 0 ==> sum >= d
    {
        if a % i == 0 && b % i == 0 {
            sum := sum + i;
        }
        i := i + 1;
    }
    
    // Prove the postcondition using the loop invariant
    forall d | 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0
        ensures sum >= d
    {
        CommonDivisorBound(a, b, d);
        assert d <= limit;
        assert 1 <= d < i;  // Since i == limit + 1 and d <= limit
    }
}
// </vc-code>