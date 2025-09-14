predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
ghost predicate isUnique(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

lemma {:induction s} UniqueAppend(s: seq<int>, x: int)
  requires isUnique(s) && !(x in s)
  ensures isUnique(s + [x])
{
}
// </vc-helpers>

// <vc-spec>
method RemoveElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in a and not in b
    ensures forall x :: x in result ==> InArray(a, x) && !InArray(b, x)
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
  var seenElements := [];
  var outputSeq := [];
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant isUnique(outputSeq)
    invariant forall x :: x in outputSeq ==> InArray(a, x) && !InArray(b, x)
    invariant forall x :: x in outputSeq ==> x in seenElements
    invariant forall x :: x in seenElements ==> (!InArray(b, x) && x in outputSeq) || (InArray(b, x) && !(x in outputSeq))
  {
    var current := a[i];
    seenElements := seenElements + [current];
    
    if !InArray(b, current) && !(current in outputSeq) {
      outputSeq := outputSeq + [current];
      UniqueAppend(outputSeq[..|outputSeq|-1], current);
    }
    i := i + 1;
  }
  
  result := outputSeq;
}
// </vc-code>

