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
// No helper code needed for this verification.
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
  var i := 0;
  result := 0;
  ghost var S: set<int> := {};
  while i < n - 2
    decreases n - 2 - i
    invariant 0 <= i <= n - 2
    invariant S == |set j | 0 <= j < i && IsMedianOfThree(p[j], p[j+1], p[j+2]) :: j|
    invariant result == |S|
    invariant 0 <= result <= n - 2
  {
    if IsMedianOfThree(p[i], p[i+1], p[i+2]) {
      ghost S := S + {i};
      result := result + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

