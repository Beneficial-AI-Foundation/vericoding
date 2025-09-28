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
/* helper modified by LLM (iteration 5): popcount double (2*n) equals popcount(n) */
lemma PopcountDouble(n: nat)
  ensures popcount(2*n) == popcount(n)
{
  if n == 0 {
  } else {
    assert (2*n) % 2 == 0;
    assert (2*n) / 2 == n;
    assert popcount(2*n) == ((2*n) % 2) + popcount((2*n)/2);
    assert popcount(2*n) == 0 + popcount(n);
    assert popcount(2*n) == popcount(n);
  }
}

/* helper modified by LLM (iteration 5): proof that power2 has one 1-bit */
lemma PopcountPower2(k: nat)
  requires k > 0
  ensures popcount(power2(k)) == 1
  decreases k
{
  if k == 1 {
    assert power2(1) == 2;
    assert popcount(2) == (2 % 2) + popcount(1);
    assert popcount(2) == 0 + popcount(1);
    assert popcount(1) == (1 % 2) + popcount(0);
    assert popcount(1) == 1 + 0;
    assert popcount(2) == 1;
  } else {
    assert power2(k) == 2 * power2(k-1);
    PopcountDouble(power2(k-1));
    PopcountPower2(k-1);
    assert popcount(power2(k)) == popcount(2 * power2(k-1));
    assert popcount(2 * power2(k-1)) == popcount(power2(k-1));
    assert popcount(power2(k-1)) == 1;
    assert popcount(power2(k)) == 1;
  }
}

/* helper modified by LLM (iteration 5): proof for power2(k)-1 popcount, uses casts to nat */
lemma PopcountPower2Minus1(k: nat)
  requires k > 0
  ensures popcount((power2(k) - 1) as nat) == k
  decreases k
{
  if k == 1 {
    assert (power2(1) - 1) as nat == 1;
    assert popcount(1) == 1;
  } else {
    assert power2(k) == 2 * power2(k-1);
    // prove power2(k-1) - 1 is non-negative so we can cast to nat
    assert power2(k-1) >= 2;
    var t := (power2(k-1) - 1) as nat;
    // show equality between the nat-cast form and 2*t + 1
    assert (power2(k) - 1) as nat == 2 * t + 1;
    assert popcount(2 * t + 1) == ((2 * t + 1) % 2) + popcount((2 * t + 1)/2);
    assert (2*t + 1) % 2 == 1;
    assert (2*t + 1) / 2 == t;
    assert popcount(2*t + 1) == 1 + popcount(t);
    PopcountPower2Minus1(k-1);
    assert popcount((power2(k) - 1) as nat) == 1 + popcount((power2(k-1) - 1) as nat);
    assert popcount((power2(k-1) - 1) as nat) == k-1;
    assert popcount((power2(k) - 1) as nat) == k;
  }
}

/* helper modified by LLM (iteration 5): bound popcount by log2_floor */
lemma PopcountBound(n: nat)
  requires n > 0
  ensures popcount(n) <= log2_floor(n) + 1
  decreases n
{
  if n == 1 {
    assert popcount(1) == 1;
    assert log2_floor(1) == 0;
    assert popcount(1) <= 0 + 1;
  } else {
    assert popcount(n) == (n % 2) + popcount(n / 2);
    assert n % 2 <= 1;
    PopcountBound(n / 2);
    assert popcount(n / 2) <= log2_floor(n / 2) + 1;
    assert popcount(n) <= 1 + (log2_floor(n / 2) + 1);
    assert log2_floor(n) == 1 + log2_floor(n / 2);
    assert 1 + (log2_floor(n / 2) + 1) == log2_floor(n) + 1;
  }
}

/* helper modified by LLM (iteration 5): absolute value symmetry for popcount */
lemma PopcountAbsNeg(x: int)
  ensures popcount(abs(x)) == popcount(abs(-x))
{
  assert abs(x) == abs(-x);
  assert popcount(abs(x)) == popcount(abs(-x));
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
  /* code modified by LLM (iteration 5): build result array and discharge postconditions by calling lemmas */
  var a := new nat[|x|];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|;
    invariant forall j :: 0 <= j < i ==> a[j] == popcount(abs(x[j]));
  {
    a[i] := popcount(abs(x[i]));
    i := i + 1;
  }

  // Now the entire array a is populated with popcounts
  i := 0;
  while i < |x|
    invariant 0 <= i <= |x|;
    invariant forall j :: 0 <= j < |x| ==> a[j] == popcount(abs(x[j]));
  {
    var n := abs(x[i]);
    assert a[i] == popcount(n);

    if n > 0 {
      PopcountBound(n);
      assert a[i] <= log2_floor(n) + 1;
    }

    if n == 0 {
      assert a[i] == 0;
    }

    if (exists k :: k > 0 && n == power2(k)) {
      var k0 :| k0 > 0 && n == power2(k0);
      PopcountPower2(k0);
      assert a[i] == 1;
    }

    if (exists k :: k > 0 && n == (power2(k) - 1) as nat) {
      var k1 :| k1 > 0 && n == (power2(k1) - 1) as nat;
      PopcountPower2Minus1(k1);
      assert a[i] == k1;
    }

    i := i + 1;
  }

  result := a[..];
}

// </vc-code>
