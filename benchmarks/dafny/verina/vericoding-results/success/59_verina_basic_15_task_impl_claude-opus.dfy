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
  result := false;
  if |a| <= 1 {
    return;
  }
  var i := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant !result ==> forall j :: 0 <= j < i ==> a[j] + 1 != a[j + 1]
    invariant result ==> exists j :: 0 <= j < |a| - 1 && a[j] + 1 == a[j + 1]
  {
    if a[i] + 1 == a[i + 1] {
      result := true;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
