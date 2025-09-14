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
  if a.Length == 0 {
    return true;
  }

  var i := 0;
  var j := a.Length - 1;

  while i < j
    invariant 0 <= i <= a.Length/2
    invariant 0 <= j <= a.Length - 1
    invariant i + j == a.Length - 1
    invariant forall k :: 0 <= k < i ==> a[k] == a[a.Length - k - 1]
  {
    if a[i] != a[j] {
      return false;
    }
    i := i + 1;
    j := j - 1;
  }
  return true;
}
// </vc-code>

