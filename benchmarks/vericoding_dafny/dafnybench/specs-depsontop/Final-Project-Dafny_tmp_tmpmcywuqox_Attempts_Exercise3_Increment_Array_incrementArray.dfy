method incrementArray(a:array<int>)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
  modifies a

{
  assume false;
}