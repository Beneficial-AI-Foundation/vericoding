// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>) returns (count: int)
    requires |a| == |b| && |b| == |c|
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): add explicit assertion to prove invariant */
{
  count := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant count == |set j: int | 0 <= j < i && a[j] == b[j] && b[j] == c[j]|
  {
    var s_i := set j | 0 <= j < i && a[j] == b[j] && b[j] == c[j];
    var s_i1 := set j | 0 <= j < i + 1 && a[j] == b[j] && b[j] == c[j];
    if a[i] == b[i] && b[i] == c[i] {
        assert s_i1 == s_i + {i};
        count := count + 1;
    } else {
        assert s_i1 == s_i;
    }
    i := i + 1;
  }
}
// </vc-code>
