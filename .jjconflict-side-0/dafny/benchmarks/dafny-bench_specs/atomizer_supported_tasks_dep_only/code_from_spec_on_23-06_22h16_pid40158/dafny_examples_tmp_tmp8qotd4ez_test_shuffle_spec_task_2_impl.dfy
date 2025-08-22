//ATOM_PLACEHOLDER_random//ATOM_PLACEHOLDER_eqMultiset_t

//ATOM_PLACEHOLDER_eqMultiset

//IMPL swap
method swap<T>(a: array<T>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}

//ATOM_PLACEHOLDER_getAllShuffledDataEntries

//ATOM_PLACEHOLDER_set_of_seq

//ATOM_PLACEHOLDER_in_set_of_seq//ATOM_PLACEHOLDER_subset_set_of_seq//ATOM_PLACEHOLDER_getRandomDataEntry