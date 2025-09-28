// <vc-preamble>
/*
 * Dafny specification for array copy functionality.
 * Provides a method to create a copy of a sequence with identical values
 * but independent memory representation.
 */

// Copy method that returns a sequence with identical values to the input
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): prove array slice equals seq */
lemma ArrayToSeqEquality<T>(b: array<T>, a: seq<T>)
  requires |a| == b.Length && (forall j :: 0 <= j < b.Length ==> b[j] == a[j])
  ensures b[..] == a
{
  var n := b.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant b[..i] == a[..i]
  {
    // show b[..i+1] == a[..i+1]
    assert 0 <= i < n;
    assert b[i] == a[i];
    // relate prefix slices to concatenation of element
    assert b[..i+1] == b[..i] + [b[i]];
    assert a[..i+1] == a[..i] + [a[i]];
    assert b[..i+1] == a[..i+1];
    i := i + 1;
  }
}

// </vc-helpers>

// <vc-spec>
method Copy<T>(a: seq<T>) returns (result: seq<T>)
  // The result has the same length as the input
  ensures |result| == |a|
  // Every element in the result equals the corresponding element in the input
  ensures forall i :: 0 <= i < |a| ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): return input sequence directly to satisfy spec */
  result := a;
}

// </vc-code>
