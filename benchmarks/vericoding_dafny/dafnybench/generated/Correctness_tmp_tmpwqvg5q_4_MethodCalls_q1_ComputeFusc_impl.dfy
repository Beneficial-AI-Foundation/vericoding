// <vc-spec>
function fusc(n: int): nat

lemma {:axiom} rule1()
  ensures fusc(0) == 0

lemma {:axiom} rule2()
  ensures fusc(1) == 1

lemma {:axiom} rule3(n:nat)
  ensures fusc(2*n) == fusc(n)

lemma {:axiom} rule4(n:nat)
  ensures fusc(2*n+1) == fusc(n) + fusc(n+1)

// <vc-helpers>
function power2(k: nat): nat
{
  if k == 0 then 1 else 2 * power2(k-1)
}

lemma power2_positive(k: nat)
  ensures power2(k) > 0
{
}

lemma power2_monotonic(i: nat, j: nat)
  requires i <= j
  ensures power2(i) <= power2(j)
{
  if i == j {
  } else {
    power2_monotonic(i, j-1);
  }
}

lemma power2_division(k: nat, n: nat)
  requires k > 0
  ensures power2(k-1) > 0
  ensures power2(k) > 0
  ensures n / power2(k-1) == 2 * (n / power2(k)) + ((n / power2(k-1)) % 2)
{
  power2_positive(k-1);
  power2_positive(k);
  
  var pk1 := power2(k-1);
  var pk := power2(k);
  
  assert pk == 2 * pk1;
  
  // Use basic division properties
  var q := n / pk1;
  var r := n % pk1;
  assert n == q * pk1 + r;
  assert 0 <= r < pk1;
  
  if r < pk1 / 2 {
    // r is in first half
    assert n / pk == q / 2;
    assert q % 2 == (n / pk1) % 2;
  } else {
    // r is in second half  
    assert n / pk == q / 2;
    assert q % 2 == (n / pk1) % 2;
  }
}

lemma power2_div_property(n: nat, i: nat)
  ensures power2(i) > 0
  ensures n / power2(i) >= 0
{
  power2_positive(i);
}
// </vc-helpers>

method ComputeFusc(N: int) returns (b: int)
  requires N >= 0 
  ensures b == fusc(N)
// </vc-spec>
// <vc-code>
{
  if N == 0 {
    rule1();
    return 0;
  }
  
  if N == 1 {
    rule2();
    return 1;
  }
  
  var a := 0;
  b := 1;
  var k := 0;
  
  // Find the position of the most significant bit
  while power2(k+1) <= N
    invariant k >= 0
    invariant power2(k) <= N
    decreases N - power2(k)
  {
    power2_positive(k+1);
    power2_monotonic(k+1, k+2);
    k := k + 1;
  }
  
  // Initialize a and b for the main loop
  power2_positive(k);
  power2_div_property(N, k);
  rule1(); // fusc(0) == 0
  rule2(); // fusc(1) == 1
  rule3(1); // fusc(2) == fusc(1) == 1
  
  // We know that N / power2(k) is either 0 or 1 since power2(k) <= N < power2(k+1)
  if N / power2(k) == 0 {
    a := 0; // fusc(0) = 0
    b := 1; // fusc(1) = 1
  } else {
    a := 1; // fusc(1) = 1
    b := 1; // fusc(2) = fusc(1) = 1, using rule3(1)
  }
  
  // Now power2(k) <= N < power2(k+1), so k is the position of MSB
  var i := k;
  var mask := power2(k);
  
  while i > 0
    invariant 0 <= i <= k
    invariant mask == power2(i)
    invariant power2(i) > 0
    invariant a == fusc(N / power2(i))
    invariant b == fusc(N / power2(i) + 1)
    decreases i
  {
    power2_positive(i);
    power2_positive(i-1);
    var next_mask := mask / 2;
    assert next_mask == power2(i-1);
    power2_div_property(N, next_mask);
    var quotient := N / next_mask;
    
    if quotient % 2 == 0 {
      // quotient is even: quotient = 2*(quotient/2)
      // fusc(quotient) = fusc(2*(quotient/2)) = fusc(quotient/2) = a
      // fusc(quotient+1) = fusc(2*(quotient/2)+1) = fusc(quotient/2) + fusc(quotient/2+1) = a + b
      rule3(quotient / 2);
      rule4(quotient / 2);
      b := a + b;
    } else {
      // quotient is odd: quotient = 2*(quotient/2)+1  
      // fusc(quotient) = fusc(2*(quotient/2)+1) = fusc(quotient/2) + fusc(quotient/2+1) = a + b
      // fusc(quotient+1) = fusc(2*(quotient/2)+2) = fusc(2*((quotient/2)+1)) = fusc(quotient/2+1) = b
      rule4(quotient / 2);
      rule3((quotient / 2) + 1);
      var old_b := b;
      b := a + b;
      a := old_b;
    }
    
    i := i - 1;
    mask := next_mask;
  }
  
  // When i == 0, mask == power2(0) == 1, so N / mask == N
  // Therefore a == fusc(N)
  b := a;
}
// </vc-code>