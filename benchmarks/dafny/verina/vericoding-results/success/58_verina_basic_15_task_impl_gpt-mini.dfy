// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsConsecutive(a: seq<int>, i: int): bool { 0 <= i < |a|-1 && a[i] + 1 == a[i+1] }
// </vc-helpers>

// <vc-spec>
method ContainsConsecutiveNumbers(a: seq<int>) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |a| - 1 && a[i] + 1 == a[i + 1]
// </vc-spec>
// <vc-code>
{
  if |a| < 2 {
    result := false;
    return;
  }
  var i := 0;
  result := false;
  while i < |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant result <==> exists k :: 0 <= k < i && a[k] + 1 == a[k+1]
  {
    if a[i] + 1 == a[i+1] {
      result := true;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
