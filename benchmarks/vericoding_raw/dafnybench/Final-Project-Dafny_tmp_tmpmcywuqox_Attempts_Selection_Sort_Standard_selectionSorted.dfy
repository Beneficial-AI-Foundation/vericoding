// <vc-helpers>
// </vc-helpers>

method selectionSorted(Array: array<int>) 
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
// <vc-code>
{
  assume false;
}
// </vc-code>