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

function popcount_nonnegative(n: nat): bool
{
    true
}

lemma popcount_nonnegative_lemma(n: nat)
    ensures popcount(n) >= 0
{
}

lemma popcount_zero()
    ensures popcount(0) == 0
{
}

lemma popcount_power2(k: nat)
    requires k >= 0
    ensures popcount(power2(k)) == 1
{
    if k == 0 {
        assert power2(0) == 1;
        assert popcount(1) == 1;
    } else {
        var p := power2(k - 1);
        assert power2(k) == 2 * p;
        popcount_power2(k - 1);
        assert popcount(p) == 1;
        assert power2(k) % 2 == 0;
        assert popcount(2 * p) == (0) + popcount(p);
    }
}

lemma popcount_power2_minus1(k: nat)
    requires k > 0
    ensures popcount(power2(k) - 1) == k
{
    if k == 1 {
        assert power2(1) == 2;
        assert power2(1) - 1 == 1;
        assert popcount(1) == 1;
    } else {
        popcount_power2_minus1(k - 1);
        assert power2(k) == 2 * power2(k - 1);
        assert power2(k) - 1 == 2 * (power2(k - 1) - 1) + 1;
        assert popcount(power2(k) - 1) == 1 + popcount(power2(k - 1) - 1);
    }
}

lemma abs_symmetric(x: int, y: int)
    requires x == -y
    ensures abs(x) == abs(y)
{
    if x >= 0 {
        assert y <= 0;
        assert abs(x) == x as nat;
        assert abs(y) == (-y) as nat;
        assert (-y) as nat == x as nat;
    } else {
        assert y >= 0;
        assert abs(x) == (-x) as nat;
        assert abs(y) == y as nat;
        assert (-x) as nat == y as nat;
    }
}

lemma popcount_abs_symmetric(x: int, y: int)
    requires x == -y
    ensures popcount(abs(x)) == popcount(abs(y))
{
    abs_symmetric(x, y);
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
  /* code modified by LLM (iteration 5): Fixed length invariant using seq conversion */
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == popcount(abs(x[j]))
    invariant forall j :: 0 <= j < i ==> result[j] >= 0
    invariant forall j :: 0 <= j < i && x[j] == 0 ==> result[j] == 0
    invariant forall j, k :: 0 <= j < i && k > 0 && x[j] == power2(k) ==> result[j] == 1
    invariant forall j, k :: 0 <= j < i && k > 0 && x[j] == power2(k) - 1 ==> result[j] == k
    invariant forall j :: 0 <= j < i && x[j] != 0 ==> result[j] <= log2_floor(abs(x[j])) + 1
    invariant forall j, l :: 0 <= j < i && 0 <= l < i && x[j] == -x[l] ==> result[j] == result[l]
  {
    var abs_val := abs(x[i]);
    result := result + [popcount(abs_val)];
    i := i + 1;
  }
}
// </vc-code>
