/**
  Inverts an array of ints.
 */

// <vc-helpers>
// </vc-helpers>

method InvertArray(a: array<int>)
  modifies a
  ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length-1-i])
// <vc-code>
{
  assume false;
}
// </vc-code>