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
  } else {
    exp_sum(b, n1-1, n2);
  }
}

lemma exp_sum_auto(b: nat)
  ensures forall n1: nat, n2: nat :: exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
{
  forall n1: nat, n2: nat
    ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2) {
    exp_sum(b, n1, n2);
  }
}

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

lemma bits_trim_front(n: nat)
  requires n > 0
  ensures from_bits(bits(n)[1..]) == n/2
{}

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

lemma from_bits_sum(s1: seq<bool>, s2: seq<bool>)
  decreases |s2|
  ensures from_bits(s1 + s2) == from_bits(s1) + exp(2, |s1|) * from_bits(s2)
{
  if s2 == [] {
    assert s1 + s2 == s1;
    assert from_bits(s2) == 0;
    assert exp(2, |s1|) * from_bits(s2) == 0;
    return;
  }
  
  var s2_head := s2[0];
  var s2_tail := s2[1..];
  assert s2 == [s2_head] + s2_tail;
  
  // Apply from_bits_append to get s1 + [s2_head]
  from_bits_append(s1, s2_head);
  
  // Apply recursive call on (s1 + [s2_head]) and s2_tail
  from_bits_sum(s1 + [s2_head], s2_tail);
  
  // Use the fact that |s1 + [s2_head]| == |s1| + 1
  assert |s1 + [s2_head]| == |s1| + 1;
  
  // Show that exp(2, |s1| + 1) == 2 * exp(2, |s1|)
  exp_sum(2, |s1|, 1);
  assert exp(2, |s1| + 1) == exp(2, |s1|) * exp(2, 1);
  assert exp(2, 1) == 2;
  assert exp(2, |s1| + 1) == 2 * exp(2, |s1|);
  
  // Now combine the results
  assert from_bits(s1 + [s2_head]) == from_bits(s1) + exp(2, |s1|) * (if s2_head then 1 else 0);
  assert from_bits(s2) == (if s2_head then 1 else 0) + 2 * from_bits(s2_tail);
  
  // The key insight: exp(2, |s1| + 1) * from_bits(s2_tail) == 2 * exp(2, |s1|) * from_bits(s2_tail)
  assert exp(2, |s1| + 1) * from_bits(s2_tail) == 2 * exp(2, |s1|) * from_bits(s2_tail);
  
  // Add the crucial intermediate step that was missing
  assert from_bits((s1 + [s2_head]) + s2_tail) == from_bits(s1 + [s2_head]) + exp(2, |s1 + [s2_head]|) * from_bits(s2_tail);
  assert (s1 + [s2_head]) + s2_tail == s1 + ([s2_head] + s2_tail);
  assert [s2_head] + s2_tail == s2;
  assert from_bits(s1 + s2) == from_bits(s1 + [s2_head]) + exp(2, |s1| + 1) * from_bits(s2_tail);
}

// <vc-helpers>
lemma exp_mul(b: nat, n1: nat, n2: nat)
  ensures exp(b, n1) * exp(b, n2) == exp(b, n1 + n2)
{
  exp_sum(b, n1, n2);
}

lemma exp_double(b: nat, n: nat)
  ensures exp(b, 2 * n) == exp(exp(b, n), 2)
  decreases n
{
  if n == 0 {
    calc {
      exp(b, 2 * 0);
      exp(b, 0);
      1;
      exp(1, 2);
      exp(exp(b, 0), 2);
    }
  } else {
    calc {
      exp(b, 2 * n);
      exp(b, n + n);
      { exp_sum(b, n, n); }
      exp(b, n) * exp(b, n);
      { exp_2_unfold(exp(b, n)); }
      exp(exp(b, n), 2);
    }
  }
}

lemma exp_power_of_two(b: nat, k: nat)
  ensures exp(b, exp(2, k)) == exp(exp(b, exp(2, k-1)), 2)
  requires k > 0
{
  assert exp(2, k) == 2 * exp(2, k-1);
  exp_double(b, exp(2, k-1));
}

lemma exp_2_unfold(b: nat)
  ensures exp(b, 2) == b * b
{
  assert exp(b, 2) == b * exp(b, 1);
  assert exp(b, 1) == b * exp(b, 0);
  assert exp(b, 0) == 1;
  assert exp(b, 1) == b * 1 == b;
  assert exp(b, 2) == b * b;
}

lemma from_bits_prefix_property(s: seq<bool>, i: nat)
  requires i <= |s|
  ensures from_bits(s[..i] + [s[i]]) == from_bits(s[..i]) + exp(2, i) * (if s[i] then 1 else 0)
  requires i < |s|
{
  from_bits_append(s[..i], s[i]);
}

lemma exp_square(b: nat, k: nat)
  ensures exp(b, exp(2, k+1)) == exp(exp(b, exp(2, k)), 2)
{
  assert exp(2, k+1) == 2 * exp(2, k);
  exp_double(b, exp(2, k));
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
  
  var bit_seq := bits(n);
  bits_from_bits(n);
  
  r := 1;
  var base := b;
  var i := 0;
  
  while i < |bit_seq|
    invariant 0 <= i <= |bit_seq|
    invariant r == exp(b, from_bits(bit_seq[..i]))
    invariant base == exp(b, exp(2, i))
    invariant from_bits(bit_seq) == n
  {
    if bit_seq[i] {
      // Prove that updating r maintains the invariant
      from_bits_prefix_property(bit_seq, i);
      assert bit_seq[..i+1] == bit_seq[..i] + [bit_seq[i]];
      assert from_bits(bit_seq[..i+1]) == from_bits(bit_seq[..i]) + exp(2, i) * 1;
      exp_sum(b, from_bits(bit_seq[..i]), exp(2, i));
      r := r * base;
    } else {
      // Prove that not updating r maintains the invariant
      from_bits_prefix_property(bit_seq, i);
      assert bit_seq[..i+1] == bit_seq[..i] + [bit_seq[i]];
      assert from_bits(bit_seq[..i+1]) == from_bits(bit_seq[..i]) + exp(2, i) * 0;
      assert from_bits(bit_seq[..i+1]) == from_bits(bit_seq[..i]);
    }
    
    // Prove that updating base maintains the invariant
    exp_2_unfold(base);
    assert base * base == exp(base, 2);
    assert base == exp(b, exp(2, i));
    exp_square(b, i);
    assert exp(exp(b, exp(2, i)), 2) == exp(b, exp(2, i+1));
    base := base * base;
    i := i + 1;
  }
  
  assert bit_seq[..|bit_seq|] == bit_seq;
  assert r == exp(b, from_bits(bit_seq));
  assert from_bits(bit_seq) == n;
}
// </vc-code>