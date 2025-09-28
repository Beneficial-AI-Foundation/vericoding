// <vc-preamble>
// Method to create a sequence of zeros of given length
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): relate array slice to array indexing */
lemma SeqSliceIndex<T>(a: array<T>, i: int)
  requires 0 <= i < a.Length
  ensures a[..][i] == a[i]
{
  assert a[..][i] == a[i];
}
// </vc-helpers>

// <vc-spec>
method zeros<T>(n: nat, zero: T) returns (result: seq<T>)
    ensures |result| == n
    // All elements are zero
    ensures forall i :: 0 <= i < |result| ==> result[i] == zero
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): allocate array with initializer lambda and return slice */
  var a := new T[n](i => zero);
  result := a[..];
}
// </vc-code>
