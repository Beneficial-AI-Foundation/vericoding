// <vc-preamble>

predicate is_prime_number(n: int)
{
  n >= 2 && forall k: int :: 2 <= k < n ==> n % k != 0
}

function seq_product(factors: seq<int>): int
  decreases |factors|
{
  if |factors| == 0 then 1
  else factors[0] * seq_product(factors[1..])
}

function power(base: int, exp: nat): int
  decreases exp
{
  if exp == 0 then 1
  else base * power(base, exp - 1)
}

lemma seq_product_append_lemma(s: seq<int>, x: int)
  ensures seq_product(s + [x]) == seq_product(s) * x
{
  if |s| == 0 {
    assert s + [x] == [x];
    assert seq_product([x]) == x;
    assert seq_product(s) == 1;
  } else {
    assert s == [s[0]] + s[1..];
    assert s + [x] == [s[0]] + (s[1..] + [x]);
    seq_product_append_lemma(s[1..], x);
    assert seq_product(s[1..] + [x]) == seq_product(s[1..]) * x;
    assert seq_product(s + [x]) == s[0] * seq_product(s[1..] + [x]);
    assert seq_product(s + [x]) == s[0] * (seq_product(s[1..]) * x);
    assert seq_product(s + [x]) == (s[0] * seq_product(s[1..])) * x;
    assert seq_product(s + [x]) == seq_product(s) * x;
  }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added precondition to reduce verification complexity */
method find_two_prime_factors(n: int, min_factor: int) returns (found: bool, p2: int, p3: int)
  requires n >= 1 && n < 50
  requires min_factor >= 2
  ensures found ==> is_prime_number(p2) && is_prime_number(p3) && n == p2 * p3 && p2 >= min_factor && p3 >= p2
  ensures !found ==> forall f1, f2 :: (f1 >= min_factor && f2 >= f1 && is_prime_number(f1) && is_prime_number(f2)) ==> n != f1 * f2
{
  var f1 := min_factor;
  while f1 * f1 <= n
    decreases n - f1
    invariant forall k, k2 :: min_factor <= k < f1 && k <= k2 && is_prime_number(k) && is_prime_number(k2) ==> n != k * k2
  {
    if is_prime_number(f1) && n % f1 == 0 {
      var f2 := n / f1;
      if f2 >= f1 && is_prime_number(f2) {
        found := true; p2 := f1; p3 := f2;
        return;
      }
    }
    f1 := f1 + 1;
  }
  found := false; p2 := 1; p3 := 1;
}
// </vc-helpers>

// <vc-spec>
method is_multiply_prime(a: int) returns (result: bool)
  requires a >= 0 && a < 100
  ensures a < 8 ==> result == false
  ensures result == true <==> (exists p1: int, p2: int, p3: int :: 
    p1 >= 2 && p2 >= 2 && p3 >= 2 && 
    is_prime_number(p1) && is_prime_number(p2) && is_prime_number(p3) &&
    a == p1 * p2 * p3)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added assert to satisfy helper precondition */
  if a < 8 {
    result := false;
    return;
  }

  result := false;

  var p1 := 2;
  while p1 * p1 * p1 <= a
    decreases a - p1
    invariant forall k1 :: 2 <= k1 < p1 && is_prime_number(k1) ==>
      !(exists k2, k3 :: is_prime_number(k2) && is_prime_number(k3) && k1 <= k2 <= k3 && a == k1 * k2 * k3)
  {
    if is_prime_number(p1) && a % p1 == 0 {
      var b := a / p1;
      assert b < 50;
      var found_two, p2, p3 := find_two_prime_factors(b, p1);
      if found_two {
        result := true;
        return;
      }
    }
    p1 := p1 + 1;
  }
}
// </vc-code>
