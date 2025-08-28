/*
*/

// <vc-helpers>
// No additional helper code or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Symmetric(a: array<int>) returns (flag: bool)
ensures flag == true ==> forall x :: 0 <= x < a.Length ==> a[x] == a[a.Length - x - 1]
ensures flag == false ==> exists x :: 0 <= x < a.Length && a[x] != a[a.Length - x - 1]
// </vc-spec>
// </vc-spec>

// <vc-code>
method SymmetricImpl(a: array<int>) returns (flag: bool)
  ensures flag == true ==> forall x :: 0 <= x < a.Length ==> a[x] == a[a.Length - x - 1]
  ensures flag == false ==> exists x :: 0 <= x < a.Length && a[x] != a[a.Length - x - 1]
{
  if a.Length == 0 {
    return true;
  }
  
  var i := 0;
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant forall k :: 0 <= k < i ==> a[k] == a[a.Length - k - 1]
  {
    if a[i] != a[a.Length - i - 1] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>
