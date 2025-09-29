// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma MulEqSelf(x: int, y: int)
  ensures x * y == x * y
{
}

// </vc-helpers>

// <vc-spec>
method CumProd(a: array<int>) returns (result: array<int>)
    requires a.Length > 0
    ensures 
        result.Length == a.Length &&
        result[0] == a[0] &&
        forall i :: 0 < i < a.Length ==> result[i] == result[i-1] * a[i]
// </vc-spec>
// <vc-code>
{
  result := new int[a.Length];
  result[0] := a[0];
  var i := 1;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant i >= 1
    invariant result.Length == a.Length
    invariant result[0] == a[0]
    invariant forall j :: 0 < j < i ==> result[j] == result[j-1] * a[j]
    decreases a.Length - i
  {
    result[i] := result[i-1] * a[i];
    i := i + 1;
  }
}

// </vc-code>
