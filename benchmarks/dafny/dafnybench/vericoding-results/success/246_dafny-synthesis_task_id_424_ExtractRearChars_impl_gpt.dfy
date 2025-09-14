

// <vc-helpers>
lemma NonEmptyAtIndex(l: seq<string>, i: int)
  requires forall k :: 0 <= k < |l| ==> |l[k]| > 0
  requires 0 <= i < |l|
  ensures |l[i]| > 0
{}
// </vc-helpers>

// <vc-spec>
method ExtractRearChars(l: seq<string>) returns (r: seq<char>)
    requires forall i :: 0 <= i < |l| ==> |l[i]| > 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i][|l[i]| - 1]
// </vc-spec>
// <vc-code>
{
  r := [];
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == l[j][|l[j]| - 1]
    decreases |l| - i
  {
    NonEmptyAtIndex(l, i);
    r := r + [l[i][|l[i]| - 1]];
    i := i + 1;
  }
}
// </vc-code>

