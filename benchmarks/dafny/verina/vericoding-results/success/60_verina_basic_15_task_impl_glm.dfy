// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ContainsConsecutiveNumbers(a: seq<int>) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |a| - 1 && a[i] + 1 == a[i + 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed loop invariant and initialization */
  if |a| < 2 {
    return false;
  }
  var i := 0;
  result := false;
  while i < |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant result == exists j :: 0 <= j < i && a[j] + 1 == a[j + 1]
  {
    if a[i] + 1 == a[i + 1] {
      result := true;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
