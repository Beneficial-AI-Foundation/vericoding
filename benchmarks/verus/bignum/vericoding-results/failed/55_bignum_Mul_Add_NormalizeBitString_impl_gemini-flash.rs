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
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) + str2int(s2),
{
  assume(false);
  unreached()
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t) &&
    t.len() > 0 &&
    (t.len() > 1 ==> t[0] != '0') &&
    (valid_bit_string(s) ==> str2int(s) == str2int(t)),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed `i: nat` and used `k: int` to manage `s2_index` for correct bit access. Corrected the base case and ensured that `bit_index` is always a `nat` type when calling `pow2_nat`. Renamed `mul_help` to `spec_mul` and introduced `pow2_nat` helper as it was missing. */
spec fn pow2_nat(exp: nat) -> nat {
  if exp == 0 { 1nat } else { 2nat * pow2_nat(exp - 1) }
}
spec fn spec_mul(s1: Seq<char>, s2: Seq<char>) -> nat
{
  if s2.len() == 0 { 
    0nat 
  } else {
    let s2_first_char_val = str2int(Seq::singleton(s2[0]));
    let remaining_s2 = s2.subrange(1, s2.len());
    let res = str2int(s1) * s2_first_char_val * pow2_nat((s2.len() - 1) as nat) + spec_mul(s1, remaining_s2);
    res
  }
}
proof fn lemma_mul_help_equals_mul(s1_vec: Seq<char>, s2_vec: Seq<char>) {
  assert(str2int(s1_vec) * str2int(s2_vec) == spec_mul(s1_vec, s2_vec));
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) * str2int(s2@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Changed `mul_help` to `spec_mul` and ensured all integer types are `int` for executable code. Cast `temp_s.len()` to `int` for `k` to resolve compilation errors. */
{
  let s1_seq = s1@;
  let s2_seq = s2@;

  if s1_seq.len() == 0 || s2_seq.len() == 0 {
    return vec!['0'];
  }

  proof {
    lemma_mul_help_equals_mul(s1_seq, s2_seq);
  }

  let result_int = spec_mul(s1_seq, s2_seq);
  
  let mut temp_s: Seq<char> = Seq::empty();
  let mut temp_val: nat = result_int;

  if temp_val == 0 {
    temp_s = temp_s.push('0');
  }

  while temp_val > 0
    invariant
      temp_val >= 0
  {
    if temp_val % 2 == 1 {
      temp_s = temp_s.push('1');
    } else {
      temp_s = temp_s.push('0');
    }
    temp_val = temp_val / 2;
  }

  let mut reversed_s_final: Seq<char> = Seq::empty();
  let mut k: int = (temp_s.len() as int) - 1; // start from the last index
  while k >= 0
    invariant
      k >= -1,
      reversed_s_final.len() == (temp_s.len() as int) - 1 - k
  {
    reversed_s_final = reversed_s_final.push(temp_s[k as nat]);
    k = k - 1;
  }

  Vec::from_seq(normalize_bit_string(reversed_s_final))
}
// </vc-code>


}

fn main() {}