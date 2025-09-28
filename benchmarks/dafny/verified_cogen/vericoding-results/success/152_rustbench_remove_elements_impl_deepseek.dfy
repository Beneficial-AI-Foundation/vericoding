// <vc-preamble>
predicate InArray(a: seq<int>, x: int)
{
    exists i :: 0 <= i < |a| && a[i] == x
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed type compatibility issues */
function InArraySeq(a: seq<int>, x: int): bool {
  exists i :: 0 <= i < |a| && a[i] == x
}

lemma RemoveHelperLemma(a: seq<int>, b: seq<int>, x: int)
  requires InArraySeq(a, x) && !InArraySeq(b, x)
  ensures exists i :: 0 <= i < |a| && a[i] == x
{
}

predicate IsUnique(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}
// </vc-helpers>

// <vc-spec>
method RemoveElements(a: array<int>, b: array<int>) returns (c: array<int>)
    ensures forall k :: 0 <= k < c.Length ==> InArray(a[..], c[k]) && !InArray(b[..], c[k])
    ensures forall i, j :: 0 <= i < j < c.Length ==> c[i] != c[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed type errors and used seq<int> instead of array<int> */
{
  var result: seq<int> := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < |result| ==> InArraySeq(a[..], result[k]) && !InArraySeq(b[..], result[k])
    invariant IsUnique(result)
  {
    if !InArraySeq(b[..], a[i]) && !InArraySeq(result, a[i]) {
      result := result + [a[i]];
    }
    i := i + 1;
  }
  c := new int[|result|];
  var j := 0;
  while j < |result|
    invariant 0 <= j <= |result|
    invariant forall k :: 0 <= k < j ==> c[k] == result[k]
  {
    c[j] := result[j];
    j := j + 1;
  }
}
// </vc-code>
