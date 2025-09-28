// <vc-preamble>
predicate AllNonzero(v: seq<int>)
{
    forall i :: 0 <= i < |v| ==> v[i] != 0
}
// </vc-preamble>

// <vc-helpers>

predicate NonZeroAt(b: array<int>, i: int)
  reads b
  requires 0 <= i < b.Length
{
  b[i] != 0
}

lemma NonZeroLemma(b: array<int>, i: int)
  requires 0 <= i < b.Length
  requires AllNonzero(b[..])
  ensures NonZeroAt(b, i)
{
}

// </vc-helpers>

// <vc-spec>
method ModVec(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a.Length == b.Length
    requires AllNonzero(b[..])
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[i] % b[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed compilation error and verified implementation */
  result := new int[a.Length];
  var index := 0;
  
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall j :: 0 <= j < index ==> result[j] == a[j] % b[j]
  {
    NonZeroLemma(b, index);
    result[index] := a[index] % b[index];
    index := index + 1;
  }
}
// </vc-code>
