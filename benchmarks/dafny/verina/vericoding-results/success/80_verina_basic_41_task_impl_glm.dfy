// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    requires a.Length > 0
    ensures result ==> (forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j])
    ensures !result ==> (exists i :: 0 <= i < a.Length && a[i] != a[0])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed quantifier and index bounds in invariants */
  result := true;
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant result ==> (forall j :: 0 <= j < i ==> a[j] == a[0])
    invariant !result ==> (exists j :: 0 <= j < i && a[j] != a[0])
  {
    if a[i] != a[0] {
      result := false;
      break;
    }
    i := i + 1;
  }
}
// </vc-code>
