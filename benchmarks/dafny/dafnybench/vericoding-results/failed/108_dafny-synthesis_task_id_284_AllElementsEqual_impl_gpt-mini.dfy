

// <vc-helpers>
lemma Helper_Noop() ensures true { }
// </vc-helpers>

// <vc-spec>
method AllElementsEqual(a: array<int>, n: int) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> a[i] == n
    ensures !result ==> exists i :: 0 <= i < a.Length && a[i] != n
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var idx := -1;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant idx == -1 ==> forall j :: 0 <= j < i ==> a[j] == n
    invariant idx != -1 ==> 0 <= idx < a.Length && a[idx] != n
  {
    if a[i] != n {
      idx := i;
      i := a.Length;
    } else {
      i := i + 1;
    }
  }
  result := idx == -1;
}
// </vc-code>

