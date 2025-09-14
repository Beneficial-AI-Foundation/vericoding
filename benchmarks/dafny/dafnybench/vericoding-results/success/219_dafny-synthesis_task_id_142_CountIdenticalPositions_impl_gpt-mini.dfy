

// <vc-helpers>
lemma CountsExt(a: seq<int>, b: seq<int>, c: seq<int>, i: int, count: int)
  requires |a| == |b| && |b| == |c|
  requires 0 <= i < |a|
  requires count == | set k: int | 0 <= k < i && a[k] == b[k] && b[k] == c[k] |
  ensures (if a[i] == b[i] && b[i] == c[i]
           then count + 1 == | set k: int | 0 <= k < i+1 && a[k] == b[k] && b[k] == c[k] |
           else count == | set k: int | 0 <= k < i+1 && a[k] == b[k] && b[k] == c[k] |)
{
  var S := set k | 0 <= k < i && a[k] == b[k] && b[k] == c[k];
  var T := set k | 0 <= k < i+1 && a[k] == b[k] && b[k] == c[k];
  if a[i] == b[i] && b[i] == c[i] {
    // T equals S union {i}
    assert forall x :: x in T <==> x in S + {i};
    assert T == S + {i};
    // {i} is disjoint from S because elements of S are < i
    assert |T| == |S + {i}|;
    assert |S + {i}| == |S| + 1;
    assert |S| == count;
  } else {
    // T equals S (i is not included because a[i]!=b[i] or b[i]!=c[i])
    assert forall x :: x in T <==> x in S;
    assert T == S;
    assert |T| == |S|;
    assert |S| == count;
  }
}
// </vc-helpers>

// <vc-spec>
method CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>) returns (count: int)
    requires |a| == |b| && |b| == |c|
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
// </vc-spec>
// <vc-code>
{
  var n := |a|;
  var i := 0;
  count := 0;
  while i < n
    invariant 0 <= i && i <= n
    invariant count == | set k: int | 0 <= k < i && a[k] == b[k] && b[k] == c[k] |
  {
    // Use lemma to relate count for range 0..i to range 0..i+1
    CountsExt(a, b, c, i, count);
    var inc := if a[i] == b[i] && b[i] == c[i] then 1 else 0;
    count := count + inc;
    i := i + 1;
  }
  assert count == | set k: int | 0 <= k < n && a[k] == b[k] && b[k] == c[k] |;
}
// </vc-code>

