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
function SumSeq(s: seq<nat>): nat
  decreases |s|
{
  if |s| == 0 then 0 else s[0] + SumSeq(s[1..])
}

function MixSeed(entropy: seq<nat>, spawnKey: seq<nat>, idx: nat): nat
  decreases |entropy|, |spawnKey|
{
  SumSeq(entropy) + SumSeq(spawnKey) + idx + 1
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
  var arr := new nat[poolSize];
  var i := 0;
  while i < poolSize
    invariant 0 <= i <= poolSize
  {
    arr[i] := MixSeed(entropy, spawnKey, i);
    i := i + 1;
  }
  result := arr[..];
}
// </vc-code>
