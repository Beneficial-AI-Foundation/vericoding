// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed type casts for subrange and seq! arguments, added lex_less spec function and lemma to connect to str2int comparison */
fn pad_zeros(v: Vec<char>, num: usize) -> (result: Vec<char>)
  requires
    valid_bit_string(v@)
  ensures
    result.len() == v.len() + num,
    result@.subrange(num as int, result.len() as int) == v@,
    forall|i: int| 0 <= i < num as int ==> result[i as usize] == '0',
    valid_bit_string(result@)
{
  let mut result = Vec::new();
  let mut i = 0;
  while i < num
      invariant
        forall|j: int| 0 <= j < result.len() ==> result[j] == '0',
        result.len() == i as int,
        i as int <= num as int
      decreases num - i
  {
    result.push('0');
    i += 1;
  }
  let mut i = 0;
  while i < v.len()
      invariant
        result.len() == num as int + i as int,
        result@.subrange(0, num as int) == seq!['0'; num as nat],
        result@.subrange(num as int, result.len() as int) == v@.subrange(0, i as int),
        i as int <= v.len() as int
      decreases v.len() - i
  {
    result.push(v[i]);
    i += 1;
  }
  result
}

spec fn lex_less(s1: Seq<char>, s2: Seq<char>) -> bool
  requires s1.len() == s2.len(), valid_bit_string(s1), valid_bit_string(s2)
  decreases s1.len()
{
  if s1.len() == 0 {
    false
  } else if s1[0] < s2[0] {
    true
  } else if s1[0] > s2[0] {
    false
  } else {
    lex_less(s1.subrange(1, s1.len()), s2.subrange(1, s2.len()))
  }
}

proof fn lemma_lex_less_iff_str2int_less(s1: Seq<char>, s2: Seq<char>)
  requires valid_bit_string(s1), valid_bit_string(s2), s1.len() == s2.len()
  ensures lex_less(s1, s2) == (str2int(s1) < str2int(s2))
by induction s1.len()
{
  if s1.len() == 0 {
    // empty sequences: false == false
  }
}
// </vc-helpers>

// <vc-spec>
fn compare(s1: Vec<char>, s2: Vec<char>) -> (res: i32)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    (str2int(s1@) < str2int(s2@)) ==> (res == -1) &&
    (str2int(s1@) == str2int(s2@)) ==> (res == 0) &&
    (str2int(s1@) > str2int(s2@)) ==> (res == 1)
  decreases str2int(s1@) + str2int(s2@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): implemented custom lex_less comparison for sequences after padding */
  let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
  let num_pad1 = max_len - s1.len();
  let num_pad2 = max_len - s2.len();
  let s1_padded = pad_zeros(s1, num_pad1);
  let s2_padded = pad_zeros(s2, num_pad2);
  proof {
    lemma_lex_less_iff_str2int_less(s1_padded@, s2_padded@);
  }
  if lex_less(s1_padded@, s2_padded@) {
    -1
  } else if lex_less(s2_padded@, s1_padded@) {
    1
  } else {
    0
  }
}
// </vc-code>


}

fn main() {}