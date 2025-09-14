

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method selectionSorted(Array: array<int>) 
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
// </vc-spec>
// <vc-code>
{
}
// </vc-code>

