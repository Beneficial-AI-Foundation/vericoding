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
function mix(a: nat, b: nat): nat { a + b + 314159 }
// </vc-helpers>

// <vc-spec>
method SeedSequence(entropy: seq<nat>, spawnKey: seq<nat>, poolSize: nat := 4) 
    returns (result: seq<nat>)
    requires poolSize > 0  // Pool size must be positive
    ensures |result| == poolSize  // Well-defined output: result has correct size
// </vc-spec>
// <vc-code>
{
  var pool := new nat[poolSize];

  // 1. Initialize pool with an arbitrary constant
  for i := 0 to poolSize {
    pool[i] := 19650218;
  }

  // 2. Absorb entropy and spawn key into the pool
  var combined_input := entropy + spawnKey;
  for i := 0 to |combined_input| {
    var idx := i % poolSize;
    pool[idx] := mix(pool[idx], combined_input[i]);
  }

  // 3. Mix the pool's state to diffuse the entropy
  var rounds := 4;
  while rounds > 0
    decreases rounds
  {
    for i := 0 to poolSize {
      // Mix each element with the previous one (circularly)
      var prev_idx := (i + poolSize - 1) % poolSize;
      pool[i] := mix(pool[i], pool[prev_idx]);
    }
    rounds := rounds - 1;
  }

  // 4. The mixed pool is the result
  result := pool[..];
}
// </vc-code>
