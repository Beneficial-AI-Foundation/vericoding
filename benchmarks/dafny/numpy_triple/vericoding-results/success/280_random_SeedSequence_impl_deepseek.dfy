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
/* helper modified by LLM (iteration 5): Fixed bitwise operations using proper bv64 shifts and conversions */
  function toBv64(n: nat): bv64
    decreases n
  {
    (n % (0x10000000000000000 as nat)) as bv64
  }

  function fromBv64(b: bv64): nat
    decreases b
  {
    b as nat
  }

  function mix(a: nat, b: nat): nat
    decreases a, b
  {
    var a_bv: bv64 := toBv64(a);
    var b_bv: bv64 := toBv64(b);
    a + b + fromBv64((a_bv << 16) + (b_bv >> 16))
  }

  function hashCombine(h1: nat, h2: nat): nat
    decreases h1, h2
  {
    mix(mix(h1, h2), mix(h2, h1))
  }

  function poolElement(idx: nat, poolSize: nat, entropy: seq<nat>, spawnKey: seq<nat>): nat
    requires poolSize > 0
    decreases idx, poolSize, entropy, spawnKey
  {
    if idx < |entropy| then entropy[idx]
    else if idx < poolSize then idx + 1
    else 0
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
  /* code modified by LLM (iteration 5): Create initial pool and apply mixing passes */
  var pool: seq<nat> := [];
  var i: nat := 0;
  
  // Initialize pool with entropy values or default values
  while i < poolSize
    invariant i <= poolSize
    invariant |pool| == i
  {
    pool := pool + [poolElement(i, poolSize, entropy, spawnKey)];
    i := i + 1;
  }
  
  // Apply hash mixing to the pool
  var j: nat := 0;
  while j < poolSize
    invariant j <= poolSize
    invariant |pool| == poolSize
  {
    var k: nat := 0;
    while k < poolSize
      invariant k <= poolSize
      invariant |pool| == poolSize
    {
      pool := pool[k := hashCombine(pool[k], pool[(k + j) % poolSize])];
      k := k + 1;
    }
    j := j + 1;
  }
  
  result := pool;
}
// </vc-code>
