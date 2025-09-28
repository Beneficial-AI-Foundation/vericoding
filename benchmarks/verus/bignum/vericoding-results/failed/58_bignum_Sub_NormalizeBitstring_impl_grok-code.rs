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

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t) &&
    t.len() > 0 &&
    (t.len() > 1 ==> t[0] != '0') &&
    (valid_bit_string(s) ==> str2int(s) == str2int(t))
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 6): Fixed compilation error by replacing 'in' with '<=' in requires and ensures clauses */spec fn pad_sequence(s: Seq<char>, length: usize) -> Seq<char>
  requires
    length <= usize::MAX,
    length >= s.len() as usize,
  ensures
    result.len() == length as nat,
    length > s.len() as usize ==> (result.take((length - s.len() as usize) as nat) =~= Seq::new((length - s.len() as usize) as nat, '0') && result.skip((length - s.len() as usize) as nat) == s),
    length <= s.len() as usize ==> result == s,
{
  Seq::new(length - s.len() as usize, '0') + s
}

fn sub_bit(aval: u32, bval: u32, bin: u32) -> (u32, u32)
  requires
    aval <= 1,
    bval <= 1,
    bin <= 1,
  ensures
    result.0 <= 1,
    result.1 <= 1,
    result.0 as int + 2 * result.1 as int == aval as int - bval as int - bin as int + (if aval as int - bval as int - bin as int < 0 { 4 } else { 0 }),
{
  let diff = aval as int - bval as int - bin as int;
  if diff >= 0 {
    (diff as u32, 0)
  } else {
    ((diff + 2) as u32, 1)
  }
}
// </vc-helpers>

// <vc-spec>
fn sub(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@) &&
    str2int(s1@) >= str2int(s2@)
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) - str2int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 6): Updated for iteration 6 with fixed helpers */
{
    let s1_seq = s1@;
    let s2_seq = s2@;
    let len1 = s1_seq.len() as usize;
    let len2 = s2_seq.len() as usize;
    let max_len = core::cmp::max(len1, len2);
    let padded_s1 = pad_sequence(s1_seq, max_len);
    let padded_s2 = pad_sequence(s2_seq, max_len);
    let mut borrow: u32 = 0;
    let mut result_seq = Seq::<char>::new(max_len as nat, '0');
    let mut i: usize = max_len;
    while i > 0
      invariant
        i <= max_len,
        borrow <= 1,
        forall|j: int| 0 <= j < max_len - i ==> valid_bit_string(result_seq.subrange(max_len - j - 1, j + 1)),
      decreases i
    {
        i = i - 1;
        let aval = if padded_s1[i] == '1' { 1u32 } else { 0u32 };
        let bval = if padded_s2[i] == '1' { 1u32 } else { 0u32 };
        let (res_bit, next_borrow) = sub_bit(aval, bval, borrow);
        result_seq = result_seq.update(i as nat, if res_bit == 1 { '1' } else { '0' });
        borrow = next_borrow;
    }
    while result_seq.len() > 1 && result_seq[0] == '0'
      invariant
        result_seq.len() > 0,
      decreases result_seq.len()
    {
        result_seq = result_seq.drop(1);
    }
    result_seq.to_vec()
}
// </vc-code>


}

fn main() {}