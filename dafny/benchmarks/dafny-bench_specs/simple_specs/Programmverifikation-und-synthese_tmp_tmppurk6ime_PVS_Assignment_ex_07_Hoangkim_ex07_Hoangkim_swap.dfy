// SPEC
//Problem01
//a)
method swap(a: array<int>, i: nat, j: nat)
  modifies a
  requires a != null && a.Length > 0 && i < a.Length && j < a.Length
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
{
}
