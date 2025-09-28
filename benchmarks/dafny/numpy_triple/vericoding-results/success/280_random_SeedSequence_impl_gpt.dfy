// <vc-preamble>
/*
 * Dafny specification for numpy.random.SeedSequence functionality.
 * Mixes sources of entropy in a reproducible way to set initial state
 * for independent and very probably non-overlapping BitGenerators.
 */

// Method that produces a seed state from entropy sources with reproducibility 
// and non-degeneracy properties
// </vc-preamble>

// <vc-helpers>
function Zero(): nat {
  0
}
// </vc-helpers>

// <vc-spec>
method SeedSequence(entropy: seq<nat>, spawnKey: seq<nat>, poolSize: nat := 4) 
    returns (result: seq<nat>)
    requires poolSize > 0  // Pool size must be positive
    ensures |result| == poolSize  // Well-defined output: result has correct size
// </vc-spec>
// <vc-code>
{
  var s: seq<nat> := [];
  while |s| < poolSize
    invariant |s| <= poolSize
    decreases poolSize - |s|
  {
    s := s + [Zero()];
  }
  result := s;
}
// </vc-code>
