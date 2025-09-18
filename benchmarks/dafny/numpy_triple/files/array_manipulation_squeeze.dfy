// <vc-preamble>
// Method to squeeze a single-element sequence to extract its value
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
