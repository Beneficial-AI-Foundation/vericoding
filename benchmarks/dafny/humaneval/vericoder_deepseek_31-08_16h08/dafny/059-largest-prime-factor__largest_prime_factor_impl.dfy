method is_prime(k: int) returns (result: bool)
  // pre-conditions-start
  requires k >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
  // post-conditions-end
{
  assume{:axiom} false;
}
function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}

// <vc-helpers>
lemma mod_lemma(a: int, b: int)
  requires a >= 0 && b > 0
  ensures 0 <= a % b < b
{
}

lemma divides_lemma(a: int, b: int)
  requires b > 0
  ensures a % b == 0 <==> exists k :: k * b == a
{
  if a % b == 0 {
    var k := a / b;
    assert k * b == a;
  } else {
    assert forall k :: k * b != a;
  }
}

lemma prime_factor_exists(n: int)
  requires n >= 2
  ensures exists f :: 2 <= f <= n && n % f == 0 && is_prime_pred(f)
{
  var f := 2;
  while f <= n
    invariant 2 <= f <= n + 1
    invariant forall i :: 2 <= i < f ==> n % i != 0
  {
    if n % f == 0 {
      prime_factor_is_prime(n, f);
      return;
    }
    f := f + 1;
  }
}

lemma prime_factor_is_prime(n: int, f: int)
  requires n >= 2 && 2 <= f <= n && n % f == 0
  requires forall i :: 2 <= i < f ==> n % i != 0
  ensures is_prime_pred(f)
{
  var i := 2;
  while i < f
    invariant 2 <= i <= f
    invariant forall j :: 2 <= j < i ==> f % j != 0
  {
    if f % i == 0 {
      assert n % i == 0;
      assert false;
    }
    i := i + 1;
  }
}

lemma factor_divides_product(n: int, f: int)
  requires n >= 1 && f >= 1
  requires n % f == 0
  ensures exists k :: k * f == n
{
  var k := n / f;
  assert k * f == n;
}

lemma preserve_prime_factor_property(current: int, f: int, largest: int, n: int)
  requires current >= 2 && f >= 2
  requires n % f == 0
  requires is_prime_pred(f)
  requires exists k :: k * largest == current
  ensures exists k :: k * f == n
  ensures f >= largest ==> (exists k' :: k' * f == (current / f))
{
  factor_divides_product(n, f);
  if f >= largest {
    var k :| k * largest == current;
    factor_divides_product(current, f);
    var k' :| k' * f == current;
    assert (current / f) * f == current;
  }
}
// </vc-helpers>

// <vc-spec>
method largest_prime_factor(n: int) returns (largest: int)
  // pre-conditions-start
  requires n >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures 1 <= largest <= n && (largest == 1 || (largest > 1 && is_prime_pred(largest)))
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var current := n;
  largest := 1;
  
  while current > 1
    invariant 1 <= current <= n
    invariant 1 <= largest <= n
    invariant largest == 1 || is_prime_pred(largest)
    invariant exists k :: k * largest == current
    decreases current
  {
    var f := 2;
    while f <= current && current % f != 0
      invariant 2 <= f <= current + 1
      invariant forall i :: 2 <= i < f ==> current % i != 0
      decreases current - f
    {
      f := f + 1;
    }
    
    if f > current {
      break;
    }
    
    assert current % f == 0;
    assert forall i :: 2 <= i < f ==> current % i != 0;
    
    prime_factor_is_prime(current, f);
    assert is_prime_pred(f);
    
    if f > largest {
      largest := f;
    }
    
    var prev_current := current;
    current := current / f;
    assert prev_current % f == 0;
    assert current * f == prev_current;
    
    // Update the invariant for exists k :: k * largest == current
    if largest > 1 {
      var k :| k * largest == prev_current;
      assert (k / f) * largest == current;
    }
  }
  assert current == 1;
}
// </vc-code>

