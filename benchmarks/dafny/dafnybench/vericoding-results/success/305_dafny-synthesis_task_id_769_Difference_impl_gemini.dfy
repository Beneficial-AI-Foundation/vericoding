// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsUnique(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

lemma UniqueAppend(s: seq<int>, x: int)
  requires IsUnique(s)
  requires x !in s
  ensures IsUnique(s + [x])
{}
// </vc-helpers>

// <vc-spec>
method Difference(a: seq<int>, b: seq<int>) returns (diff: seq<int>)
    ensures forall x :: x in diff <==> (x in a && x !in b)
    ensures forall i, j :: 0 <= i < j < |diff| ==> diff[i] != diff[j]
// </vc-spec>
// <vc-code>
{
  diff := [];
  var i := 0;
  while i < |a|
    decreases |a| - i
    invariant 0 <= i <= |a|
    invariant IsUnique(diff)
    invariant forall x :: x in diff ==> x in a[..i] && x !in b
    invariant forall x :: x in a[..i] && x !in b ==> x in diff
  {
    var current := a[i];
    if current !in b && current !in diff {
      diff := diff + [current];
    }
    i := i + 1;
  }
}
// </vc-code>
