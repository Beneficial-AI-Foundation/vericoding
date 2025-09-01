

// <vc-helpers>
lemma StepCardinality(s: seq<int>, i: int)
  requires 0 <= i
  requires i + 1 <= |s|
  ensures |set j | 0 <= j < i + 1 && s[j] != s[|s| - 1 - j]| ==
          |set j | 0 <= j < i && s[j] != s[|s| - 1 - j]| + (if s[i] != s[|s| - 1 - i] then 1 else 0)
{
  var old := set j | 0 <= j < i && s[j] != s[|s| - 1 - j];
  var new := set j | 0 <= j < i + 1 && s[j] != s[|s| - 1 - j];
  if s[i] != s[|s| - 1 - i] {
    assert new == old + {i};
    assert i !in old;
    assert |new| == |old| + 1;
  } else {
    assert new == old;
    assert |new| == |old|;
  }
}
// </vc-helpers>

// <vc-spec>
method smallest_change(s: seq<int>) returns (c: int)
  // post-conditions-start
  ensures c == |set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  var half := n / 2;
  var i := 0;
  c := 0;
  while i < half
    invariant 0 <= i <= half
    invariant half == |s
// </vc-code>

