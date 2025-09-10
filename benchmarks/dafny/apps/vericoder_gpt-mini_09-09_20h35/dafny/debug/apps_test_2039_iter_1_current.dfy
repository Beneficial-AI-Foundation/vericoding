predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 && |a| == n
}

function CountLocalExtrema(n: int, a: seq<int>): int
    requires ValidInput(n, a)
{
    |set i | 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))|
}

predicate IsLocalExtremum(a: seq<int>, i: int)
    requires 0 <= i < |a|
{
    1 <= i < |a| - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))
}

// <vc-helpers>
// (No helper code needed)
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures result >= 0
    ensures n <= 2 ==> result == 0
    ensures n > 2 ==> result <= n - 2
    ensures result == CountLocalExtrema(n, a)
// </vc-spec>
// <vc-code>
{
  if n <= 2 {
    result := 0;
    return;
  }
  result := 0;
  ghost var s: set<int> := {};
  var k := 1;
  while k < n - 1
    invariant 1 <= k <= n - 1
    invariant result == |s|
    invariant forall j :: j in s <==> 1 <= j < k && IsLocalExtremum(a, j)
    decreases n - k
  {
    if IsLocalExtremum(a, k) {
      result := result + 1;
      ghost s := s + {k};
    }
    k := k + 1;
  }
}
// </vc-code>

