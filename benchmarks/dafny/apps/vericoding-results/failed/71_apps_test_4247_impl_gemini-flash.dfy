// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `to` in for loop in Dafny is inclusive, so the condition should be `i < n - 2` to correctly define the range for `i` between `0` and `n - 3`. */
function ComputeResult(n: int, p: seq<int>): int
    requires ValidInput(n, p)
    ensures this >= 0
    ensures this <= n - 2
    ensures this == CountMedianElements(p, n)
{
    var count := 0;
    for i := 0 to n - 3
        invariant 0 <= i <= n - 2
        invariant count == |set k | 0 <= k < i && IsMedianOfThree(p[k], p[k + 1], p[k + 2]) :: k|
    {
        if IsMedianOfThree(p[i], p[i+1], p[i+2]) {
            count := count + 1;
        }
    }
    return count;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: seq<int>) returns (result: int)
    requires ValidInput(n, p)
    ensures result >= 0
    ensures result <= n - 2
    ensures result == CountMedianElements(p, n)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Calling helper function to compute result */
{
  result := ComputeResult(n, p);
}
// </vc-code>
