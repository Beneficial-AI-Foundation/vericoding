// <vc-preamble>
predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}
// </vc-preamble>

// <vc-helpers>
predicate InSeq(s: seq<int>, x: int) { x in s }
// </vc-helpers>

// <vc-spec>
method Intersection(a: array<int>, b: array<int>) returns (result: seq<int>)

    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))

    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Replaced a failing loop invariant with a simpler, provable one. */
  result := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: InSeq(result, x) ==> InArray(b, x)
    invariant forall k, l :: 0 <= k < l < |result| ==> result[k] != result[l]
    invariant forall x :: InSeq(result, x) ==> InArray(a, x)
  {
    var x := a[i];
    if InArray(b, x) && !InSeq(result, x) {
      result := result + [x];
    }
    i := i + 1;
  }
}
// </vc-code>
