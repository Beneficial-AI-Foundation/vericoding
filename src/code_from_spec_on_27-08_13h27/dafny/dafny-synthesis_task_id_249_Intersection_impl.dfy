predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
function SeqFromArray(a: array<int>): seq<int>
  reads a
{
  seq(a.Length, i requires 0 <= i < a.Length reads a => a[i])
}

lemma UniqueElementsInSeq(s: seq<int>)
  ensures forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Intersection(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in both a and b
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// </vc-spec>

// <vc-code>
method ComputeIntersection(a: array<int>, b: array<int>) returns (result: seq<int>)
  ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
  var seqA := SeqFromArray(a);
  var seqB := SeqFromArray(b);
  var tempResult: seq<int> := [];
  var i := 0;
  
  while i < |seqA|
    invariant 0 <= i <= |seqA|
    invariant forall x :: x in tempResult ==> (x in seqA && x in seqB)
    invariant forall k, l :: 0 <= k < l < |tempResult| ==> tempResult[k] != tempResult[l]
  {
    var current := seqA[i];
    if current in seqB && current !in tempResult
    {
      tempResult := tempResult + [current];
    }
    i := i + 1;
  }
  
  result := tempResult;
}
// </vc-code>
