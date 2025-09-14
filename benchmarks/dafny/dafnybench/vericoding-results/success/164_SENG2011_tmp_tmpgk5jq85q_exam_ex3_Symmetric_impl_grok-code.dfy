/*
*/

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Symmetric(a: array<int>) returns (flag: bool)
ensures flag == true ==> forall x :: 0 <= x < a.Length ==> a[x] == a[a.Length - x - 1]
ensures flag == false ==> exists x :: 0 <= x < a.Length && a[x] != a[a.Length - x - 1]
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant forall j :: 0 <= j < i ==> a[j] == a[a.Length - 1 - j]
  {
    if a[i] != a[a.Length - 1 - i] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

