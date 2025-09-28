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

// </vc-helpers>

// <vc-spec>
method SeedSequence(entropy: seq<nat>, spawnKey: seq<nat>, poolSize: nat := 4) 
    returns (result: seq<nat>)
    requires poolSize > 0  // Pool size must be positive
    ensures |result| == poolSize  // Well-defined output: result has correct size
// </vc-spec>
// <vc-code>
{
  var pool := seq(poolSize, i => 0);
  
  // Mix entropy into pool
  var i := 0;
  while i < |entropy|
    invariant 0 <= i <= |entropy|
    invariant |pool| == poolSize
  {
    if i < poolSize {
      pool := pool[i := pool[i] + entropy[i]];
    }
    i := i + 1;
  }
  
  // Mix spawnKey into pool
  var j := 0;
  while j < |spawnKey|
    invariant 0 <= j <= |spawnKey|
    invariant |pool| == poolSize
  {
    if j < poolSize {
      pool := pool[j := pool[j] + spawnKey[j]];
    }
    j := j + 1;
  }
  
  result := pool;
}
// </vc-code>
