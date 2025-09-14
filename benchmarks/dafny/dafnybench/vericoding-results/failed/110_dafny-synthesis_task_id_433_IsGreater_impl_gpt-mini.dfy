

// <vc-helpers>
{:allow_warnings}
module SuppressWarnings {}
// </vc-helpers>

// <vc-spec>
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> n > a[i]
    ensures !result ==> exists i :: 0 <= i < a.Length && n <= a[i]
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> n > a[j]
  {
    if !(n > a[i]) {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

