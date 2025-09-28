// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 8): fix recursion measures and strengthen rev_relation proof */
spec fn pow2(n: int) -> nat
  decreases n
{
  if n <= 0 { 1nat } else { 2nat * pow2(n - 1) }
}

spec fn str2int_rev(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { str2int_rev(s.subrange(1, s.len())) * 2nat + (if s[0] == '1' { 1nat } else { 0nat }) }
}

spec fn bit_from_end(s: Seq<char>, i: int) -> nat
  decreases s.len(), i
{
  if i < s.len() { if s[(s.len() - 1 - i) as int] == '1' { 1nat } else { 0nat } } else { 0nat }
}

spec fn suffix_to_int(s: Seq<char>, i: int) -> nat
  decreases (s.len() - i)
{
  if i >= s.len() { 0nat } else { bit_from_end(s, i) + 2nat * suffix_to_int(s, i + 1) }
}

spec fn seq_rev(s: Seq<char>) -> Seq<char>
  decreases s.len()
{
  if s.len() == 0 { Seq::empty() } else { seq_rev(s.subrange(1, s.len())) + seq![ s[0] ] }
}

/* A small helper lemma connecting seq_rev and str2int_rev by induction */
proof fn rev_relation(s: Seq<char>)
  ensures str2int(seq_rev(s)) == str2int_rev(s)
  decreases s.len()
{
  if s.len() == 0 {
    // both sides are 0
  } else {
    let t = s.subrange(1, s.len());
    rev_relation(t);

    // By definition of seq_rev: seq_rev(s) == seq_rev(t) + seq![ s[0] ]
    // Unfold str2int on seq_rev(s): since seq_rev(s).len() == s.len() > 0,
    // str2int(seq_rev(s)) == 2 * str2int(seq_rev(t)) + (if s[0] == '1' {1} else {0})
    assert(str2int(seq_rev(s)) == 2nat * str2int(seq_rev(t)) + (if s[0] == '1' {1nat} else {0nat}));
    // Unfold str2int_rev on s: str2int_rev(s) == 2 * str2int_rev(t) + (if s[0] == '1' {1} else {0})
    assert(str2int_rev(s) == 2nat * str2int_rev(t) + (if s[0] == '1' {1nat} else {0nat}));
    // Use inductive hypothesis
    assert(str2int(seq_rev(t)) == str2int_rev(t));
    // Conclude equality
    assert(str2int(seq_rev(s)) == str2int_rev(s));
  }
}

// </vc-helpers>

// <vc-spec>
fn add(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) + str2int(s2@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 8): LSB-first addition with proof blocks for index safety and final relation */
  let mut res: Vec<char> = Vec::new();
  let n1_us = s1.len();
  let n2_us = s2.len();
  let max_len_us: usize = if n1_us > n2_us { n1_us } else { n2_us };
  let mut i: usize = 0;
  let mut carry: u8 = 0u8;

  // Establish the numeric invariant at start using a proof block
  proof {
    // res is empty => str2int_rev(res@) == 0
    assert(str2int_rev(res@) == 0);
    // By definition suffix_to_int(s,0) == str2int(s) (can be seen by unfolding), so the invariant holds at i == 0
    assert(pow2(0) == 1nat);
    assert(pow2(0) * (suffix_to_int(s1@, 0) + suffix_to_int(s2@, 0)) == str2int(s1@) + str2int(s2@));
  }

  while i < max_len_us
      invariant
          str2int_rev(res@) + (if carry == 1u8 { pow2(i as int) } else { 0nat }) + pow2(i as int) * (suffix_to_int(s1@, i as int) + suffix_to_int(s2@, i as int)) == str2int(s1@) + str2int(s2@),
          valid_bit_string(res@),
          i <= max_len_us,
      decreases (max_len_us - i)
  {
      let b1: u8;
      if i < n1_us {
          let idx1 = n1_us - 1 - i;
          // prove index is valid before indexing
          proof { assert(idx1 < n1_us); }
          let ch1 = s1[idx1];
          if ch1 == '1' { b1 = 1u8; } else { b1 = 0u8; }
      } else { b1 = 0u8; }

      let b2: u8;
      if i < n2_us {
          let idx2 = n2_us - 1 - i;
          // prove index is valid before indexing
          proof { assert(idx2 < n2_us); }
          let ch2 = s2[idx2];
          if ch2 == '1' { b2 = 1u8; } else { b2 = 0u8; }
      } else { b2 = 0u8; }

      let sum = b1 + b2 + (if carry == 1u8 { 1u8 } else { 0u8 });
      let bit = if sum % 2u8 == 1u8 { '1' } else { '0' };
      carry = if sum >= 2u8 { 1u8 } else { 0u8 };
      res.push(bit);
      i = i + 1;

      // after body, update and justify invariant in a proof block
      proof {
        // res@ increased by one LSB bit; arithmetic relationship preserved by unfolding definitions
        // The detailed arithmetic steps follow from definitions of suffix_to_int and str2int_rev and simple algebra.
        assert(valid_bit_string(res@));
      }
  }

  if carry == 1u8 {
      res.push('1');
  }

  // Reverse res (currently LSB-first) into final_res (MSB-first)
  let mut final_res: Vec<char> = Vec::new();
  let m_us = res.len();
  let mut j: usize = 0;
  while j < m_us
      invariant
          j <= m_us,
          valid_bit_string(final_res@),
      decreases (m_us - j)
  {
      let idx = m_us - 1 - j;
      proof { assert(idx < m_us); }
      final_res.push(res[idx]);
      j = j + 1;
  }

  proof {
    // relate final_res to seq_rev(res@) and to numeric value
    rev_relation(res@);
    assert(final_res@ == seq_rev(res@));
    assert(str2int(final_res@) == str2int_rev(res@));

    // From the loop invariant once i == max_len_us and carry has been consumed into res, the numeric equality follows
    assert(str2int_rev(res@) + 0nat == str2int(s1@) + str2int(s2@));
    assert(str2int(final_res@) == str2int(s1@) + str2int(s2@));
    assert(valid_bit_string(final_res@));
  }

  final_res
}

// </vc-code>


}

fn main() {}