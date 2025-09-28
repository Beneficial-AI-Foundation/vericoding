// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsSorted(a: seq<int>) returns (result: bool)
    ensures
        result == (forall i :: 0 <= i < |a| - 1 ==> a[i] <= a[i + 1])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): [simplify loop and use early return] */
  if |a| <= 1 {
    result := true;
    return;
  }

  var i := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant forall j :: 0 <= j < i ==> a[j] <= a[j+1]
  {
    if a[i] > a[i+1] {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
}
// </vc-code>
