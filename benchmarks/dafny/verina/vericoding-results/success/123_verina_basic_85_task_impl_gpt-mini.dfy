// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma ReverseIndexBounds(len: int, i: int)
  requires len >= 0 && 0 <= i < len
  ensures 0 <= len - 1 - i < len
{
  // From i < len we get len - 1 - i >= 0 and len - 1 - i < len
  assert len - 1 - i >= 0;
  assert len - 1 - i < len;
}

// </vc-helpers>

// <vc-spec>
method Reverse(a: array<int>) returns (result: array<int>)
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[a.Length - 1 - i]
// </vc-spec>
// <vc-code>
{
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == a[a.Length - 1 - j]
  {
    ReverseIndexBounds(a.Length, i);
    result[i] := a[a.Length - 1 - i];
    i := i + 1;
  }
}

// </vc-code>
