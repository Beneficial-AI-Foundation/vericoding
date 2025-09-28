// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma IndexBound(i: int, l: int, m: int)
  requires 0 <= i < l
  requires l == m
  ensures 0 <= i < m
{
}

// </vc-helpers>

// <vc-spec>
method GreaterEqual(a: array<int>, b: array<int>) returns (result: array<bool>)
    requires a.Length == b.Length
    ensures 
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == (a[i] >= b[i])
// </vc-spec>
// <vc-code>
{
  result := new bool[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == (a[j] >= b[j])
  {
    assert i < b.Length;
    result[i] := a[i] >= b[i];
    i := i + 1;
  }
}
// </vc-code>
