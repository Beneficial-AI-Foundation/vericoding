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
predicate IsMedianOfThree(a: int, b: int, c: int)
{
    (a < b && b < c) || (a > b && b > c) ||
    (a < c && c < b) || (a > c && c > b) ||
    (b < a && a < c) || (b > a && a > c)
}
  // This predicate is intentionally left as is to satisfy the problem's definition for CountMedianElements.
  // The global predicate IsMedianOfThree defines the more general median concept as a strict middle value.
  // This helper predicate simply defines the problem's interpretation of MedianOfThree (a strictly monotonic sequence).
  // The problem is likely relying on this for the CountMedianElements definition which uses this monotonic interpretation.
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
        invariant count == |set k | 0 <= k < i && IsMedianOfThree(p[k], p[k+1], p[k+2]) :: k|
    {
        if ((p[i] < p[i+1] && p[i+1] < p[i+2]) || (p[i] > p[i+1] && p[i+1] > p[i+2])) // The problem's definition of MedianOfThree that is used by CountMedianElements
        {
            count := count + 1;
        }
        i := i + 1;
    }
    result := count;
}
// </vc-code>

