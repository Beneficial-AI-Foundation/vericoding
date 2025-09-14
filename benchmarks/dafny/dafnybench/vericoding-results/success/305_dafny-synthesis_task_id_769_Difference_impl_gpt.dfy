

// <vc-helpers>
function UniqueDiffAux(a: seq<int>, b: seq<int>, seen: set<int>): seq<int>
  decreases |a|
  ensures forall x :: x in UniqueDiffAux(a, b, seen) <==> (x in a && x !in b && x !in seen)
  ensures forall i, j :: 0 <= i < j < |UniqueDiffAux(a, b, seen)| ==> UniqueDiffAux(a, b, seen)[i] != UniqueDiffAux(a, b, seen)[j]
{
  if |a| == 0 then
    []
  else if a[0] in b || a[0] in seen then
    UniqueDiffAux(a[1..], b, seen)
  else
    [a[0]] + UniqueDiffAux(a[1..], b, seen + {a[0]})
}

function UniqueDiff(a: seq<int>, b: seq<int>): seq<int>
  ensures forall x :: x in UniqueDiff(a, b) <==> (x in a && x !in b)
  ensures forall i, j :: 0 <= i < j < |UniqueDiff(a, b)| ==> UniqueDiff(a, b)[i] != UniqueDiff(a, b)[j]
{
  UniqueDiffAux(a, b, {})
}
// </vc-helpers>

// <vc-spec>
method Difference(a: seq<int>, b: seq<int>) returns (diff: seq<int>)
    ensures forall x :: x in diff <==> (x in a && x !in b)
    ensures forall i, j :: 0 <= i < j < |diff| ==> diff[i] != diff[j]
// </vc-spec>
// <vc-code>
{
  diff := UniqueDiff(a, b);
}
// </vc-code>

