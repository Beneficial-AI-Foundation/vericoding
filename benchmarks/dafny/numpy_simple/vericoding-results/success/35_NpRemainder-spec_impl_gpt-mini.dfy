// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma ArrayLengthNonNegative(a: array<int>)
  ensures a.Length >= 0
{
}

// </vc-helpers>

// <vc-spec>
method remainder(a: array<int>, b: array<int>) returns (result: array<int>)
    requires 
        a.Length == b.Length
    requires
        forall i :: 0 <= i < b.Length ==> b[i] != 0
    ensures
        result.Length == a.Length
    ensures
        forall i :: 0 <= i < result.Length ==> result[i] == a[i] % b[i]
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  result := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> result[j] == a[j] % b[j]
  {
    result[i] := a[i] % b[i];
    i := i + 1;
  }
}

// </vc-code>
