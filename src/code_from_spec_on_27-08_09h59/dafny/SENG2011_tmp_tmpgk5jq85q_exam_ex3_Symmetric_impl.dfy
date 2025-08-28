/*
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Symmetric(a: array<int>) returns (flag: bool)
ensures flag == true ==> forall x :: 0 <= x < a.Length ==> a[x] == a[a.Length - x - 1]
ensures flag == false ==> exists x :: 0 <= x < a.Length && a[x] != a[a.Length - x - 1]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var i := 0;
  flag := true;
  
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant flag == true ==> forall x :: 0 <= x < i ==> a[x] == a[a.Length - x - 1]
    invariant flag == false ==> exists x :: 0 <= x < i && a[x] != a[a.Length - x - 1]
  {
    if a[i] != a[a.Length - i - 1] {
      flag := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
