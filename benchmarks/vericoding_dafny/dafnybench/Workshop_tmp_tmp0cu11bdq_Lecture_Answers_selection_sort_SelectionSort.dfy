//https://homepage.cs.uiowa.edu/~tinelli/classes/181/Fall21/Tools/Dafny/Examples/selection-sort.shtml



predicate sorted (a: array<int>)
    requires a != null
    reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}


// Selection sort on arrays

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>) 
  modifies a
  ensures sorted(a)
  //ensures multiset(old(a[..])) == multiset(a[..])
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>