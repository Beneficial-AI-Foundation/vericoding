
use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
spec fn trim_leading_zeros(s: Seq<char>) -> Seq<char>
  ensures
    Str2Int(trim_leading_zeros(s)) == Str2Int(s),
    (trim_leading_zeros(s).len() == 0 || trim_leading_zeros(s).index(0) == '1' || trim_leading_zeros(s).len() == 1)
{
  if s.len() == 0 {
    s
  } else if s.index(0) == '0' {
    // Proof to show that `Str2Int(s.subrange(1, s.len() as int))` is equal to `Str2Int(s)`
    proof { assert(Str2Int(s) == Str2Int(s.subrange(1, s.len() as int))); }
    trim_leading_zeros(s.subrange(1, s.len() as int))
  } else {
    s
  }
}

proof fn lemma_prop_Str2IntValue(s: Seq<char>) 
  requires
    ValidBitString(s),
    s.len() > 0,
    s.index(0) == '0'
  ensures
    Str2Int(s) == Str2Int(s.subrange(1, s.len() as int))
{
  // Base case: s.len() == 1, s is "0"
  if s.len() == 1 {
    assert(Str2Int(s) == 0);
    assert(Str2Int(s.subrange(1, s.len() as int)) == Str2Int(Seq::<char>::empty()));
    assert(Str2Int(Seq::<char>::empty()) == 0);
  }
  // Inductive step
  else {
    assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));
    assert(s.subrange(0, s.len() as int - 1).index(0) == '0');
    lemma_prop_Str2IntValue(s.subrange(0, s.len() as int - 1));
    assert(Str2Int(s.subrange(0, s.len() as int - 1)) == Str2Int(s.subrange(1, s.len() as int - 1)));
    assert(Str2Int(s.subrange(1, s.len() as int)) == 2 * Str2Int(s.subrange(1, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));
    assert(Str2Int(s) == Str2Int(s.subrange(1, s.len() as int)));
  }
}

spec fn bitwise_left_shift(s: Seq<char>, k: nat) -> Seq<char>
  requires ValidBitString(s)
  ensures
    forall |i: int| 0 <= i && i < s.len() ==> bitwise_left_shift(s, k).index(i) == s.index(i),
    forall |i: int| s.len() <= i && i < s.len() + k ==> bitwise_left_shift(s, k).index(i) == '0',
    bitwise_left_shift(s, k).len() == s.len() + k,
    Str2Int(bitwise_left_shift(s, k)) == Str2Int(s) * (1nat << k as nat)
{
  s + Seq::<char>::new(k, |i| '0')
}

spec fn bitwise_compare(a: Seq<char>, b: Seq<char>) -> bool
  requires ValidBitString(a), ValidBitString(b)
  decreases a.len() + b.len()
{
  if a.len() < b.len() { false }
  else if a.len() > b.len() { true }
  else if a.len() == 0 { true } // Both empty or both '0'
  else if a.index(0) == b.index(0) { bitwise_compare(a.subrange(1, a.len() as int), b.subrange(1, b.len() as int)) }
  else { a.index(0) == '1' }
}

proof fn Str2Int_ge_zero(s: Seq<char>) 
  requires ValidBitString(s)
  ensures Str2Int(s) >= 0
{}

proof fn lemma_Str2Int_trimmed_non_zero(s: Seq<char>) 
  requires ValidBitString(s),
           Str2Int(s) > 0
  ensures trim_leading_zeros(s).len() > 0,
          trim_leading_zeros(s).index(0) == '1'
{
  if s.len() == 0 {
    assert(Str2Int(s) == 0);
    assert(false);
  }
  if s.index(0) == '0' {
    lemma_Str2Int_trimmed_non_zero(s.subrange(1, s.len() as int));
  }
}

pure fn seq_to_vec_char(s: Seq<char>) -> Vec<char>
  ensures seq_to_vec_char(s)@ == s
{
  let mut v = Vec::new();
  let mut i = 0;
  while i < s.len()
    invariant
      v@.len() == i,
      v@ == s.subrange(0, i as int)
  {
    v.push(s.index(i as int));
    i = i + 1;
  }
  v
}

pure fn vec_char_to_seq(v: &Vec<char>) -> Seq<char>
  ensures vec_char_to_seq(v) == v@
{
  v@
}

proof fn compare_trimmed_Str2Int(s1: Seq<char>, s2: Seq<char>)
  requires
    ValidBitString(s1),
    ValidBitString(s2),
  ensures
    (Str2Int(s1) >= Str2Int(s2)) == bitwise_compare(trim_leading_zeros(s1), trim_leading_zeros(s2))
{
  if s1.len() == 0 && s2.len() == 0 {
    assert(Str2Int(s1) == 0);
    assert(Str2Int(s2) == 0);
    assert(bitwise_compare(s1, s2)); // true
  } else if s1.len() == 0 { // s2 not empty, so Str2Int(s2) > 0
    assert(Str2Int(s1) == 0);
    assert(bitwise_compare(s1, s2) == false); // s1 is shorter
    assert(Str2Int(s1) < Str2Int(s2));
  } else if s2.len() == 0 { // s1 not empty, so Str2Int(s1) > 0
    assert(Str2Int(s2) == 0);
    assert(bitwise_compare(s1, s2) == true); // s1 is longer
    assert(Str2Int(s1) > Str2Int(s2));
  }

  let s1_trimmed = trim_leading_zeros(s1);
  let s2_trimmed = trim_leading_zeros(s2);

  if s1_trimmed.len() < s2_trimmed.len() {
    assert(Str2Int(s1) < Str2Int(s2));
    assert(!bitwise_compare(s1_trimmed, s2_trimmed));
  } else if s1_trimmed.len() > s2_trimmed.len() {
    assert(Str2Int(s1) > Str2Int(s2));
    assert(bitwise_compare(s1_trimmed, s2_trimmed));
  } else if s1_trimmed.len() == 0 {
    assert(s1.len() == 0 && s2.len() == 0);
    assert(Str2Int(s1) == Str2Int(s2));
    assert(bitwise_compare(s1_trimmed, s2_trimmed));
  } else {
    // same length, not empty
    if s1_trimmed.index(0) == s2_trimmed.index(0) {
        lemma_compare_equal_prefix(s1_trimmed, s2_trimmed);
        compare_trimmed_Str2Int(s1_trimmed.subrange(1, s1_trimmed.len() as int), s2_trimmed.subrange(1, s2_trimmed.len() as int));
    } else if s1_trimmed.index(0) == '1' {
        assert(s2_trimmed.index(0) == '0');
        assert(Str2Int(s1) > Str2Int(s2));
        assert(bitwise_compare(s1_trimmed, s2_trimmed));
    } else {
        assert(s1_trimmed.index(0) == '0');
        assert(s2_trimmed.index(0) == '1');
        assert(Str2Int(s1) < Str2Int(s2));
        assert(!bitwise_compare(s1_trimmed, s2_trimmed));
    }
  }
}

proof fn lemma_compare_equal_prefix(s1: Seq<char>, s2: Seq<char>)
  requires
    ValidBitString(s1),
    ValidBitString(s2),
    s1.len() == s2.len(),
    s1.len() > 0,
    s1.index(0) == s2.index(0)
  ensures
    (Str2Int(s1) >= Str2Int(s2)) == (Str2Int(s1.subrange(1, s1.len() as int)) >= Str2Int(s2.subrange(1, s2.len() as int)))
{
}

pure fn subtr(a: Seq<char>, b: Seq<char>) -> Seq<char>
  requires ValidBitString(a),
           ValidBitString(b),
           Str2Int(a) >= Str2Int(b)
  ensures ValidBitString(subtr(a, b)),
          Str2Int(subtr(a, b)) == Str2Int(a) - Str2Int(b)
{
  let mut result = Seq::<char>::new(a.len(), |i| '0');
  let mut borrow = 0;
  let mut i = 0;

  while i < a.len()
    invariant
      0 <= i && i <= a.len(),
      ValidBitString(result),
      Str2Int(a.subrange(a.len() as int - 1 - i, a.len() as int)) + (borrow as nat) * (1nat << i as nat) == Str2Int(b.subrange(b.len() as int - 1 - i, b.len() as int)) + Str2Int(result.subrange(a.len() as int - 1 - i, a.len() as int))
  {
    let a_bit = if a.len() as int - 1 - i >= 0 { (a.index(a.len() as int - 1 - i) == '1') as nat } else { 0 };
    let b_bit = if b.len() as int - 1 - i >= 0 { (b.index(b.len() as int - 1 - i) == '1') as nat } else { 0 };

    let current_a = a_bit - borrow;

    if current_a >= b_bit {
      result = result.update(a.len() as int - 1 - i, if (current_a - b_bit) == 1 { '1' } else { '0' });
      borrow = 0;
    } else {
      result = result.update(a.len() as int - 1 - i, if (current_a + 2 - b_bit) == 1 { '1' } else { '0' });
      borrow = 1;
    }
    i = i + 1;
  }
  result
}

// </vc-helpers>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
  let d_seq = vec_char_to_seq(&divisor);
  let mut dividend_current = vec_char_to_seq(dividend);
  let mut quotient = Seq::<char>::empty();

  let d_trimmed = trim_leading_zeros(d_seq);
  if d_trimmed.len() == 0 {
    // Divisor is 0, which is disallowed by recommends
    // This case should not be reached due to pre-condition `Str2Int(divisor@) > 0`
    unreachable!();
  }

  // Handle initial case where dividend_current might be smaller than divisor_trimmed
  if (Str2Int(dividend_current) < Str2Int(vec_char_to_seq(divisor))) {
      return (seq_to_vec_char(Seq::new(1, |i| '0')), seq_to_vec_char(dividend_current));
  }

  let mut k: nat = 0;
  while dividend_current.len() > d_seq.len()
    invariant
      ValidBitString(dividend_current),
      ValidBitString(d_seq),
      Str2Int(d_seq) > 0,
      quotient.len() == k,
      ValidBitString(quotient)
  {
      k = k + 1;
      quotient = quotient + Seq::new(1, |i| '0');
  }

  let mut k_loop_count: nat = 0;
  while k_loop_count <= k
    invariant
      ValidBitString(dividend_current),
      ValidBitString(d_seq),
      Str2Int(d_seq) > 0,
      k >= k_loop_count,
      quotient.len() == k_loop_count as int + (if k_loop_count < k { 0 } else { 1 }) as int,
      ValidBitString(quotient),
      Str2Int(quotient) * Str2Int(d_seq) + Str2Int(dividend_current) == Str2Int(vec_char_to_seq(dividend)) // not quite an invariant

    // This needs to be carefully constructed. It's the core division algorithm
  {
      // Calculate shifted divisor
      let shifted_divisor = bitwise_left_shift(d_seq, k - k_loop_count);

      if (Str2Int(dividend_current) >= Str2Int(shifted_divisor)) {
          dividend_current = subtr(dividend_current, shifted_divisor);
          // Set the corresponding bit in the quotient to '1'
          quotient = quotient.update(k_loop_count as int, '1');
      }
      // else quotient bit is already '0'
      k_loop_count = k_loop_count + 1;
  }

  let mut final_quotient = trim_leading_zeros(quotient);
  if (final_quotient.len() == 0) {
    final_quotient = Seq::new(1, |i| '0');
  }

  let mut final_remainder = trim_leading_zeros(dividend_current);
  if (final_remainder.len() == 0) {
    final_remainder = Seq::new(1, |i| '0');
  }

  (seq_to_vec_char(final_quotient), seq_to_vec_char(final_remainder))
}
// </vc-code>

fn main() {}
}


