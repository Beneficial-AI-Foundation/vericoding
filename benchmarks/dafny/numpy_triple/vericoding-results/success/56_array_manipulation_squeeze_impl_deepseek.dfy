// <vc-preamble>
// Method to squeeze a single-element sequence to extract its value
// </vc-preamble>

// <vc-helpers>
lemma SqueezeLemma<T>(a: seq<T>, b: seq<T>)
  requires |a| == 1 && |b| == 1
  requires a[0] == b[0]
  ensures a == b
{
  assert a == [a[0]];
  assert b == [b[0]];
}
// </vc-helpers>

// <vc-spec>
method squeeze<T>(a: seq<T>) returns (result: T)
  // Input must be a sequence of exactly size 1
  requires |a| == 1
  
  // The result equals the first (and only) element of the input sequence
  ensures result == a[0]
  
  // Injectivity property: if two size-1 sequences have the same squeezed value, they are equal
  ensures forall b: seq<T> :: |b| == 1 && b[0] == result ==> a == b
  
  // All elements in the sequence equal the result (trivial for size 1, but captures the uniqueness)
  ensures forall i: int :: 0 <= i < |a| ==> a[i] == result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed compilation error by removing unnecessary type constraint */
  result := a[0];
  
  // The injectivity property is satisfied by the SqueezeLemma helper
  // The element-wise equality is trivial for size-1 sequences
}
// </vc-code>
