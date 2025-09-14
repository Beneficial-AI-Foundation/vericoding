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
function CountMedianElementsPrefix(p: seq<int>, k: int): int
    requires 0 <= k <= |p| - 2
{
    if k == 0 then 0
    else CountMedianElementsPrefix(p, k-1) + (if IsMedianOfThree(p[k-1], p[k], p[k+1]) then 1 else 0)
}

function CountMedianElements(p: seq<int>, n: int): int
    requires ValidInput(n, p)
{
    CountMedianElementsPrefix(p, n-2)
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
{
  var count := 0;
  for i := 0 to n-3
    invariant 0 <= i <= n-2
    invariant count == CountMedianElementsPrefix(p, i)
  {
    if IsMedianOfThree(p[i], p[i+1], p[i+2]) {
      count := count + 1;
    }
  }
  return count;
}
// </vc-code>

