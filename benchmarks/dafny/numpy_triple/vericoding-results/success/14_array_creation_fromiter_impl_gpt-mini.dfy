// <vc-preamble>
// Method to create a new sequence containing the first count elements from an iterable sequence
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): proofs for append length and index properties */
lemma AppendSingletonLength<T>(s: seq<T>, x: T)
  ensures |s + [x]| == |s| + 1
{
  // length of concatenation equals sum of lengths
  assert |s + [x]| == |s| + |[x]|;
  assert |[x]| == 1;
}

/* helper modified by LLM (iteration 2): proof for indexing into appended sequence */
lemma AppendIndex<T>(s: seq<T>, x: T, k: int)
  requires 0 <= k <= |s|
  ensures (s + [x])[k] == (if k < |s| then s[k] else x)
{
  if k < |s| {
    assert (s + [x])[k] == s[k];
  } else {
    // k == |s|
    assert (s + [x])[k] == x;
  }
}

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
/* code modified by LLM (iteration 2): initialize r as empty seq<T> and build result by appending elements */
{
  var r: seq<T> := [];
  var i := 0;
  while i < count
    invariant 0 <= i <= count
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == iterable[j]
  {
    r := r + [iterable[i]];
    i := i + 1;
  }
  result := r;
}

// </vc-code>
