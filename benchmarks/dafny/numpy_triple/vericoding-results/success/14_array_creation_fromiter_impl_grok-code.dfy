// <vc-preamble>
// Method to create a new sequence containing the first count elements from an iterable sequence
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FromIter<T>(iterable: seq<T>, count: nat) returns (result: seq<T>)
    // Precondition: we can't read more elements than available in the iterable
    requires count <= |iterable|
    // Postcondition: result has exactly count elements
    ensures |result| == count
    // Postcondition: each element in result corresponds to the element at the same index in iterable
    ensures forall i :: 0 <= i < count ==> result[i] == iterable[i]
// </vc-spec>
// <vc-code>
{
  result := iterable[..count];
}
// </vc-code>
