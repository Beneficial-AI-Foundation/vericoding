// <vc-preamble>
/*
 * Dafny specification for numpy.empty functionality.
 * Returns a new array of given length without initializing entries to specific values.
 * The array contains arbitrary values but is guaranteed to have the specified length.
 */
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method empty(n: nat) returns (result: array<real>)
  // Postcondition: returned array has exactly the requested length
  ensures result.Length == n
  // Postcondition: returned array is freshly allocated
  ensures fresh(result)
  // Postcondition: all array positions contain valid real values (guaranteed by Dafny's type system)
  ensures forall i :: 0 <= i < result.Length ==> result[i] == result[i]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
