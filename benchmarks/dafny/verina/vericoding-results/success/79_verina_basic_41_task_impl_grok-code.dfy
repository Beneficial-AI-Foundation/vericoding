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
/* code modified by LLM (iteration 2): added loop invariants to prove the postcondition */
{
  result := true;
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant result ==> (forall k :: 0 <= k < i ==> a[k] == a[0])
    invariant !result ==> (exists k :: 0 <= k < i && a[k] != a[0])
  {
    if a[i] != a[0] {
      result := false;
    }
    i := i + 1;
  }
}
// </vc-code>
