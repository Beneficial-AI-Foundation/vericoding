// <vc-preamble>
predicate InArray(a: seq<int>, x: int)
{
    exists i :: 0 <= i < |a| && a[i] == x
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RemoveElements(a: array<int>, b: array<int>) returns (c: array<int>)
    ensures forall k :: 0 <= k < c.Length ==> InArray(a[..], c[k]) && !InArray(b[..], c[k])
    ensures forall i, j :: 0 <= i < j < c.Length ==> c[i] != c[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added loop invariant and decreases clause to ensure verification */
  var result: seq<int> := [];
  var i := 0;
  while i < a.Length
    decreases a.Length - i
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < |result| ==> InArray(a[..i], result[k]) && !InArray(b[..], result[k])
    invariant forall k1, k2 :: 0 <= k1 < k2 < |result| ==> result[k1] != result[k2]
  {
    var x := a[i];
    if !InArray(b[..], x) && !InArray(result, x)
    {
      result := result + [x];
    }
    i := i + 1;
  }
  c := new int[|result|](k requires 0 <= k < |result| => result[k]);
}
// </vc-code>
