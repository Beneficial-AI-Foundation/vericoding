// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function AreConsecutive(x: int, y: int): bool {
  x + 1 == y
}
// </vc-helpers>

// <vc-spec>
method ContainsConsecutiveNumbers(a: seq<int>) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |a| - 1 && a[i] + 1 == a[i + 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added guard for array length < 2 to avoid loop invariant violation */
  if |a| < 2 {
    return false;
  }
  var i := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant forall j :: 0 <= j < i ==> !AreConsecutive(a[j], a[j+1])
  {
    if AreConsecutive(a[i], a[i+1]) {
      return true;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>
