// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed to 'function' and provided reverse index computation */
function RevIndex(n: nat, i: nat): nat
  requires i < n
{
  n - 1 - i
}
// </vc-helpers>

// <vc-spec>
method Reverse(a: array<int>) returns (result: array<int>)
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[a.Length - 1 - i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement reverse array construction with loop invariants */
  result := new int[a.Length];
  var n := a.Length;
  var i := 0;
  while i < n
    invariant 0 <= i
    invariant i <= n
    invariant result.Length == n
    invariant forall j :: 0 <= j < i ==> result[j] == a[n - 1 - j]
  {
    result[i] := a[n - 1 - i];
    i := i + 1;
  }
}
// </vc-code>
