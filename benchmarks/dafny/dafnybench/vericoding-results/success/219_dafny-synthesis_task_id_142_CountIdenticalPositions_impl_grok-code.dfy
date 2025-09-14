

// <vc-helpers>
// Helpers section unchanged - no updates needed
// </vc-helpers>

// <vc-spec>
method CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>) returns (count: int)
    requires |a| == |b| && |b| == |c|
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
// </vc-spec>
// <vc-code>
{
  ghost var S: set<int> := {};
  count := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant S == set k: int | 0 <= k < i && a[k] == b[k] && b[k] == c[k]
    invariant count == |S|
  {
    if a[i] == b[i] && b[i] == c[i] {
      S := S + {i};
      count := count + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

