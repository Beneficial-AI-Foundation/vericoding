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
function mixEntropy(a: nat, b: nat): nat { (a * 73 + b * 31) % 2147483647 }

/* helper modified by LLM (iteration 4): fixed type error by casting if expressions to nat */
function generatePool(entropy: seq<nat>, spawnKey: seq<nat>, poolSize: nat): seq<nat>
    requires poolSize > 0
    ensures |generatePool(entropy, spawnKey, poolSize)| == poolSize
{
    seq<nat>(poolSize, j requires 0 <= j < poolSize =>
        mixEntropy((if |entropy| > 0 then entropy[j % |entropy|] else 0) as nat, 
                   (if |spawnKey| > 0 then spawnKey[j % |spawnKey|] else 0) as nat)
    )
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
  /* code modified by LLM (iteration 4): updated to use fixed helper function */
  result := generatePool(entropy, spawnKey, poolSize);
}
// </vc-code>
