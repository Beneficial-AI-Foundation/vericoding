function psum(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum(s[..(|s|)-1]) + s[ |s| - 1 ]
}

// <vc-helpers>
lemma psum_slice_step(ops: seq<int>, i: int)
  requires 0 <= i < |ops|
  ensures psum(ops[..i+1]) == psum(ops[..i]) + ops[i]
{
  // By definition of psum on a non-empty sequence s:
  // psum(s) == psum(s[..|s|-1]) + s[|s|-1].
  // Apply this to s := ops[..i+1], noting |ops[..i+1]| = i+1.
  assert psum(ops[..i+1]) == psum((ops[..i+1])[..(i+1)-1]) + (ops[..i+1])[(i+1)-1];
  assert (ops[..i+1])[(i+1)-1] == ops[i];
  assert (ops[..i+1])[..(i+1)-1] == ops[..i];
}
// </vc-helpers>

// <vc-spec>
method below_zero(ops: seq<int>) returns (res : bool)
    // post-conditions-start
    ensures res ==> forall i : int :: 0 <= i <= |ops| ==> psum(ops[..i]) >= 0
    ensures !res ==> exists i : int :: 0 <= i <= |ops| && psum(ops[..i]) < 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var sum := 0;
  while i < |ops|
    invariant 0 <= i <= |ops|
    invariant sum == psum(ops[..i])
    invariant forall j :: 0 <= j <= i ==> psum(ops[..j]) >= 0
    decreases |ops| - i
  {
    var newsum := sum + ops[i];
    assert psum(ops[..i+1]) == psum(ops[..i]) + ops[i];
    if newsum < 0 {
      res := false;
      return;
    }
    sum := newsum;
    i := i + 1;
  }
  res := true;
  return;
}
// </vc-code>

