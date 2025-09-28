// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 {
    0nat
  } else {
    2nat * str2int(s.subrange(0, s.len() - 1)) + 
    (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn compare_unequal(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
    s1.len() > 0,
    s1.len() > 1 ==> s1[0] != '0',
    s2.len() > 0,
    s2.len() > 1 ==> s2[0] != '0',
    s1.len() > s2.len()
  ensures 
    str2int(s1) < str2int(s2) ==> res == -1,
    str2int(s1) == str2int(s2) ==> res == 0,
    str2int(s1) > str2int(s2) ==> res == 1
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
spec fn is_zero(s: Seq<char>) -> bool {
  s.len() == 1 && s[0] == '0'
}

/* helper modified by LLM (iteration 4): fixed type conversions for Seq indexing */
proof fn lemma_str2int_gt_zero(s: Seq<char>)
  requires
    valid_bit_string(s),
    !is_zero(s)
  ensures
    str2int(s) > 0
{
  if s.len() == 1 {
    assert(s[0] == '1');
  } else {
    lemma_str2int_gt_zero(s.subrange(0, s.len() - 1));
  }
}

/* helper modified by LLM (iteration 4): fixed type conversions for Seq indexing */
proof fn lemma_str2int_prefix_inequality(s: Seq<char>, t: Seq<char>)
  requires
    valid_bit_string(s),
    valid_bit_string(t),
    s.len() > t.len()
  ensures
    str2int(s) > str2int(t)
{
  if t.len() == 0 {
    assert(str2int(t) == 0);
    lemma_str2int_gt_zero(s);
  } else {
    lemma_str2int_prefix_inequality(s.subrange(0, s.len() - 1), t.subrange(0, t.len() - 1));
  }
}

fn compare_lengths(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
  requires
    valid_bit_string(s1),
    valid_bit_string(s2)
  ensures
    s1.len() > s2.len() ==> res == 1,
    s1.len() == s2.len() ==> res == 0,
    s1.len() < s2.len() ==> res == -1
{
  if s1.len() > s2.len() {
    1
  } else if s1.len() < s2.len() {
    -1
  } else {
    0
  }
}

/* helper modified by LLM (iteration 4): removed ghost type conversions */
fn compare_equal_length(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
  requires
    valid_bit_string(s1),
    valid_bit_string(s2),
    s1.len() == s2.len()
  ensures
    str2int(s1) < str2int(s2) ==> res == -1,
    str2int(s1) == str2int(s2) ==> res == 0,
    str2int(s1) > str2int(s2) ==> res == 1
{
  if s1.len() == 0 {
    0
  } else {
    proof {
      let last_idx = s1.len() - 1;
      assert(last_idx < s1.len());
      assert(last_idx < s2.len());
    }
    let last_char_s1 = s1.last();
    let last_char_s2 = s2.last();
    let prefix_s1 = s1.subrange(0, s1.len() - 1);
    let prefix_s2 = s2.subrange(0, s2.len() - 1);
    let prefix_compare = compare_equal_length(prefix_s1, prefix_s2);
    
    if prefix_compare != 0 {
      prefix_compare
    } else if last_char_s1 == last_char_s2 {
      0
    } else if last_char_s1 == '1' {
      1
    } else {
      -1
    }
  }
}
// </vc-helpers>

// <vc-spec>
fn compare(s1: Vec<char>, s2: Vec<char>) -> (res: i32)
  requires valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    str2int(s1@) < str2int(s2@) ==> res == -1,
    str2int(s1@) == str2int(s2@) ==> res == 0,
    str2int(s1@) > str2int(s2@) ==> res == 1
  decreases str2int(s1@) + str2int(s2@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): fixed Seq type usage */
  let s1_seq = s1@;
  let s2_seq = s2@;
  
  let len_compare = compare_lengths(s1_seq, s2_seq);
  
  if len_compare != 0 {
    len_compare
  } else {
    compare_equal_length(s1_seq, s2_seq)
  }
}
// </vc-code>


}

fn main() {}