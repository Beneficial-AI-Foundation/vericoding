predicate ValidInput(n: int, p: seq<int>)
{
    |p| == n && n >= 3
}

function CountMedianElements(p: seq<int>, n: int): int
    requires ValidInput(n, p)
{
    |set i | 0 <= i < n - 2 && IsMedianOfThree(p[i], p[i + 1], p[i + 2]) :: i|
}

predicate IsMedianOfThree(a: int, b: int, c: int)
{
    (a < b < c) || (a > b > c)
}

// <vc-helpers>
predicate IsStrictlyMonotonic(a: int, b: int, c: int)
{
    (a < b && b < c) || (a > b && b > c)
}
// The original `IsMedianOfThree` predicate in the file is problematic because it's duplicated.
// The `CountMedianElements` function seems to use the "strictly monotonic" definition implicitly.
// To resolve the duplicate name error and maintain the intended logic
// for `CountMedianElements`, we introduce `IsStrictlyMonotonic`.
// The `solve` method's loop condition also uses this stricter definition.
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: seq<int>) returns (result: int)
    requires ValidInput(n, p)
    ensures result >= 0
    ensures result <= n - 2
    ensures result == CountMedianElements(p, n)
// </vc-spec>
// <vc-code>
{
    var count := 0;
    var i := 0;
    while i < n - 2
        invariant 0 <= i <= n - 2
        invariant count == |set k | 0 <= k < i && IsStrictlyMonotonic(p[k], p[k+1], p[k+2]) :: k|
    {
        if (IsStrictlyMonotonic(p[i], p[i+1], p[i+2]))
        {
            count := count + 1;
        }
        i := i + 1;
    }
    result := count;
}
// </vc-code>

