// <vc-preamble>
// Helper function to compute the number of 1-bits (popcount) in a natural number
function popcount(n: nat): nat
    decreases n
{
    if n == 0 then 0 else (n % 2) + popcount(n / 2)
}

// Helper function to compute absolute value of an integer
function abs(x: int): nat
{
    if x >= 0 then x as nat else (-x) as nat
}

// Helper function to compute powers of 2
function power2(k: nat): nat
    decreases k
{
    if k == 0 then 1 else 2 * power2(k - 1)
}

// Helper function to compute logarithm base 2 (floor)
function log2_floor(n: nat): nat
    requires n > 0
    decreases n
{
    if n <= 1 then 0 else 1 + log2_floor(n / 2)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemmas to properly prove popcount properties for all values */
lemma PopcountBoundedByLog2(n: nat)
    requires n > 0
    ensures popcount(n) <= log2_floor(n) + 1
    decreases n
{
    if n <= 1 {
        // Base case: popcount(1) = 1, log2_floor(1) + 1 = 0 + 1 = 1
    } else {
        PopcountBoundedByLog2(n / 2);
    }
}

lemma Power2HasOnebit(k: nat)
    requires k > 0
    ensures popcount(power2(k)) == 1
    decreases k
{
    if k == 1 {
        // Base case: power2(1) = 2, popcount(2) = 1
        assert power2(1) == 2;
        assert popcount(2) == popcount(1) + 0 == 1;
    } else {
        Power2HasOnebit(k - 1);
        assert power2(k) == 2 * power2(k-1);
        assert popcount(power2(k)) == popcount(power2(k-1)) == 1;
    }
}

lemma Power2Minus1HasKBits(k: nat)
    requires k > 0
    ensures popcount(power2(k) - 1) == k
    decreases k
{
    if k == 1 {
        assert power2(1) == 2;
        assert power2(1) - 1 == 1;
        assert popcount(1) == 1;
    } else {
        Power2Minus1HasKBits(k - 1);
        assert power2(k) == 2 * power2(k-1);
        var prev := power2(k-1) - 1;
        var curr := power2(k) - 1;
        assert curr == 2 * power2(k-1) - 1 == power2(k-1) + (power2(k-1) - 1);
        assert popcount(curr) == popcount(power2(k-1)) + popcount(power2(k-1) - 1);
        Power2HasOnebit(k-1);
        assert popcount(curr) == 1 + (k-1) == k;
    }
}

lemma Power2Properties(k: nat)
    requires k > 0
    ensures power2(k) >= 1
    ensures power2(k) - 1 >= 0
{
    if k == 1 {
        assert power2(1) == 2;
    } else {
        Power2Properties(k - 1);
    }
}

lemma ProvePopcountForAllPowers(x: int, count: nat)
    requires count == popcount(abs(x))
    ensures forall k :: k > 0 && x == power2(k) ==> count == 1
    ensures forall k :: k > 0 && x == power2(k) - 1 ==> count == k
{
    forall k | k > 0 && x == power2(k)
        ensures count == 1
    {
        Power2HasOnebit(k);
        assert count == popcount(abs(x)) == popcount(power2(k)) == 1;
    }
    
    forall k | k > 0 && x == power2(k) - 1
        ensures count == k
    {
        Power2Properties(k);
        Power2Minus1HasKBits(k);
        assert count == popcount(abs(x)) == popcount(power2(k) - 1) == k;
    }
}
// </vc-helpers>

// <vc-spec>
method bitwise_count(x: seq<int>) returns (result: seq<nat>)
    // Output has same length as input
    ensures |result| == |x|
    
    // Primary specification: each output element is popcount of absolute value of input
    ensures forall i :: 0 <= i < |x| ==> result[i] == popcount(abs(x[i]))
    
    // Popcount is bounded by the number of bits needed to represent the absolute value
    ensures forall i :: 0 <= i < |x| && x[i] != 0 ==> result[i] <= log2_floor(abs(x[i])) + 1
    
    // Zero inputs produce zero outputs  
    ensures forall i :: 0 <= i < |x| ==> x[i] == 0 ==> result[i] == 0
    
    // Powers of 2 have exactly one bit set
    ensures forall i, k :: 0 <= i < |x| && k > 0 && x[i] == power2(k) ==> result[i] == 1
    
    // Powers of 2 minus 1 have k consecutive 1-bits
    ensures forall i, k :: 0 <= i < |x| && k > 0 && x[i] == power2(k) - 1 ==> result[i] == k
    
    // Popcount is always non-negative
    ensures forall i :: 0 <= i < |x| ==> result[i] >= 0
    
    // For negative inputs, uses absolute value
    ensures forall i :: 0 <= i < |x| && x[i] < 0 ==> result[i] == popcount(abs(x[i]))
    
    // Sign invariance: opposite values have same popcount
    ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| && x[i] == -x[j] ==> result[i] == result[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Use helper lemma to prove all power properties at once */
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == popcount(abs(x[k]))
    invariant forall k :: 0 <= k < i && x[k] != 0 ==> result[k] <= log2_floor(abs(x[k])) + 1
    invariant forall k, j :: 0 <= k < i && j > 0 && x[k] == power2(j) ==> result[k] == 1
    invariant forall k, j :: 0 <= k < i && j > 0 && x[k] == power2(j) - 1 ==> result[k] == j
  {
    var count := popcount(abs(x[i]));
    
    if x[i] != 0 {
      PopcountBoundedByLog2(abs(x[i]));
    }
    
    // Prove power properties using helper lemma
    ProvePopcountForAllPowers(x[i], count);
    
    result := result + [count];
    i := i + 1;
  }
}
// </vc-code>
