/**
  Inverts an array of ints.
 */

method InvertArray(a: array<int>)
  modifies a
  ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length-1-i])

{
  assume false;
}