

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>) returns (count: int)
    requires |a| == |b| && |b| == |c|
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
// </vc-spec>
// <vc-code>
{
  count := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant count >= 0
    invariant count == | set j: int | 0 <= j < i && a[j] == b[j] && b[j] == c[j] |
    decreases |a| - i
  {
    if a[i] == b[i] && b[i] == c[i] {
      assert (set j: int | 0 <= j < i + 1 && a[j] == b[j] && b[j] == c[j]) ==
             ((set j: int | 0 <= j < i && a[j] == b[j] && b[j] == c[j]) + {i});
      assert i !in (set j: int | 0 <= j < i && a[j] == b[j] && b[j] == c[j]);
      count := count + 1;
    } else {
      assert (set j: int | 0 <= j < i + 1 && a[j] == b[j] && b[j] == c[j]) ==
             (set j: int | 0 <= j < i && a[j] == b[j] && b[j] == c[j]);
    }
    i := i + 1;
  }
}
// </vc-code>

