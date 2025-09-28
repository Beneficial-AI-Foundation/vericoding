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
/* helper modified by LLM (iteration 5): Added lemma for power2 properties */
lemma PopcountBound(n: nat)
    requires n > 0
    ensures popcount(n) <= log2_floor(n) + 1
    decreases n
{
    if n == 1 {
        assert popcount(1) == 1;
        assert log2_floor(1) == 0;
    } else {
        PopcountBound(n / 2);
        assert popcount(n) == (n % 2) + popcount(n / 2);
        assert log2_floor(n) == 1 + log2_floor(n / 2);
        assert popcount(n / 2) <= log2_floor(n / 2) + 1;
        assert (n % 2) <= 1;
        assert popcount(n) <= 1 + log2_floor(n / 2) + 1;
        assert popcount(n) <= log2_floor(n) + 1;
    }
}

lemma Power2Popcount(k: nat)
    requires k > 0
    ensures popcount(power2(k)) == 1
    decreases k
{
    if k == 1 {
        assert power2(1) == 2;
        assert popcount(2) == popcount(1) + 0 == 1;
    } else {
        Power2Popcount(k - 1);
        assert power2(k) == 2 * power2(k - 1);
        var n := power2(k - 1);
        assert popcount(2 * n) == popcount(n) + 0;
        assert popcount(power2(k)) == 1;
    }
}

lemma Power2Minus1Popcount(k: nat)
    requires k > 0
    ensures power2(k) >= 1
    ensures power2(k) - 1 >= 0
    ensures popcount(power2(k) - 1) == k
    decreases k
{
    if k == 1 {
        assert power2(1) == 2;
        assert power2(1) - 1 == 1;
        assert popcount(1) == 1;
    } else {
        assert power2(k) == 2 * power2(k - 1);
        assert power2(k) >= 2;
        Power2Minus1Popcount(k - 1);
        var n := power2(k - 1) - 1;
        assert power2(k) - 1 == 2 * power2(k - 1) - 1;
        assert 2 * power2(k - 1) - 1 == 2 * n + 1;
        assert popcount(2 * n + 1) == 1 + popcount(n);
        assert popcount(n) == k - 1;
        assert popcount(power2(k) - 1) == k;
    }
}

lemma Power2Properties(k: nat)
    requires k > 0
    ensures power2(k) > 0
{
    // trivial since power2 is always positive for k >= 0
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
  /* code modified by LLM (iteration 5): Pre-compute lemmas for special cases before adding to result */
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == popcount(abs(x[j]))
    invariant forall j :: 0 <= j < i && x[j] != 0 ==> result[j] <= log2_floor(abs(x[j])) + 1
    invariant forall j, k :: 0 <= j < i && k > 0 && x[j] == power2(k) ==> result[j] == 1
    invariant forall j, k :: 0 <= j < i && k > 0 && x[j] == power2(k) - 1 ==> result[j] == k
  {
    var absVal := abs(x[i]);
    var count := popcount(absVal);
    
    // Establish properties before adding to result
    if absVal > 0 {
      PopcountBound(absVal);
    }
    
    // Check for power of 2 cases
    ghost var k := 1;
    while k <= 64  // reasonable upper bound for bit operations
      invariant 1 <= k <= 65
    {
      if power2(k) == absVal {
        Power2Popcount(k);
        assert popcount(absVal) == 1;
        assert count == 1;
      } else if power2(k) > absVal && k > 1 && power2(k-1) < absVal && absVal == power2(k) - 1 {
        Power2Minus1Popcount(k);
        assert popcount(absVal) == k;
        assert count == k;
      }
      
      if power2(k) > absVal {
        break;
      }
      k := k + 1;
    }
    
    result := result + [count];
    
    // Assert the invariants hold for the newly added element
    assert result[i] == popcount(abs(x[i]));
    if x[i] != 0 {
      assert result[i] <= log2_floor(abs(x[i])) + 1;
    }
    
    // Re-establish invariants for powers of 2
    assert forall j, m :: 0 <= j < i && m > 0 && x[j] == power2(m) ==> result[j] == 1;
    assert forall j, m :: 0 <= j < i && m > 0 && x[j] == power2(m) - 1 ==> result[j] == m;
    
    // For the current element
    if exists m :: m > 0 && x[i] == power2(m) {
      ghost var m :| m > 0 && x[i] == power2(m);
      Power2Popcount(m);
      assert result[i] == 1;
    }
    if exists m :: m > 0 && x[i] == power2(m) - 1 {
      ghost var m :| m > 0 && x[i] == power2(m) - 1;
      Power2Properties(m);
      Power2Minus1Popcount(m);
      assert result[i] == m;
    }
    
    i := i + 1;
  }
}
// </vc-code>
