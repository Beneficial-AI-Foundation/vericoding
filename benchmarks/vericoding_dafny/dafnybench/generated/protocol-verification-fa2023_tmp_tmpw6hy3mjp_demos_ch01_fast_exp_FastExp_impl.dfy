function sum(s: seq<int>, i: nat): int
    requires i <= |s|
{
    if i == 0 then 0 else sum(s, i-1) + s[i-1]
}

function exp(b: nat, n: nat): nat {
  if n == 0 then 1
  else b * exp(b, n-1)
}

lemma exp_sum(b: nat, n1: nat, n2: nat)
  ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
{
  if n1 == 0 {
    return;
  }
  exp_sum(b, n1-1, n2);
}

// this "auto" version of exp_sum is convenient when we want to let Z3 figure
// out how to use exp_sum rather than providing all the arguments ourselves
lemma exp_sum_auto(b: nat)
  ensures forall n1: nat, n2: nat :: exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
{
  forall n1: nat, n2: nat
    ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2) {
    exp_sum(b, n1, n2);
  }
}

/* A key aspect of this proof is that each iteration handles one bit of the
 * input. The best way I found to express its loop invariants is to compute and
 * refer to this sequence of bits, even if the code never materializes it. */

function bits(n: nat): seq<bool>
  decreases n
{
  if n == 0 then []
  else [if (n % 2 == 0) then false else true] + bits(n/2)
}

function from_bits(s: seq<bool>): nat {
  if s == [] then 0
  else (if s[0] then 1 else 0) + 2 * from_bits(s[1..])
}

lemma bits_from_bits(n: nat)
  ensures from_bits(bits(n)) == n
{
}

lemma from_bits_append(s: seq<bool>, b: bool)
  ensures from_bits(s + [b]) == from_bits(s) + exp(2, |s|) * (if b then 1 else 0)
{
  if s == [] {
    return;
  }
  assert s == [s[0]] + s[1..];
  from_bits_append(s[1..], b);
  // from recursive call
  assert from_bits(s[1..] + [b]) == from_bits(s[1..]) + exp(2, |s|-1) * (if b then 1 else 0);
  exp_sum(2, |s|-1, 1);
  assert (s + [b])[1..] == s[1..] + [b]; // observe
  assert from_bits(s + [b]) == (if s[0] then 1 else 0) + 2 * from_bits(s[1..] + [b]);
}

// <vc-helpers>
lemma exp_double(b: nat, k: nat)
  ensures exp(b, 2 * k) == exp(exp(b, k), 2)
{
  if k == 0 {
    return;
  }
  exp_sum(b, k, k);
}

lemma exp_powers_of_two(b: nat, k: nat)
  ensures exp(b, exp(2, k)) == exp(exp(b, exp(2, k-1)), 2)
  requires k > 0
{
  assert exp(2, k) == 2 * exp(2, k-1) by {
    exp_sum(2, 1, k-1);
  }
  exp_double(b, exp(2, k-1));
}

lemma bits_length_decreases(n: nat)
  ensures n > 0 ==> |bits(n/2)| < |bits(n)|
{
}

lemma bits_length_nonneg(n: nat)
  ensures |bits(n)| >= 0
{
}

lemma exp_mult_property(b: nat, n: nat, m: nat)
  ensures exp(b, n * m) == exp(exp(b, n), m)
{
  if m == 0 {
    return;
  }
  exp_mult_property(b, n, m-1);
  exp_sum(b, n * (m-1), n);
}
// </vc-helpers>

method FastExp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    return 1;
  }
  
  r := 1;
  var current_b := b;
  var remaining := n;
  
  exp_sum_auto(b);
  
  while remaining > 0
    invariant 0 <= remaining <= n
    invariant current_b == exp(b, n - remaining)
    invariant r * exp(current_b, remaining) == exp(b, n)
    decreases remaining
  {
    if remaining % 2 == 1 {
      r := r * current_b;
      remaining := remaining - 1;
    } else {
      current_b := current_b * current_b;
      remaining := remaining / 2;
    }
  }
}
// </vc-code>