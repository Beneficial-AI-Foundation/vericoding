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
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t),
    t.len() > 0,
    t.len() > 1 ==> t[0] != '0',
    valid_bit_string(s) ==> str2int(s) == str2int(t),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed invariant syntax and added lemma support */
proof fn lemma_str2int_leading_zero(s: Seq<char>) 
  requires valid_bit_string(s) && s.len() > 0 && s[0] == '0',
  ensures str2int(s) == str2int(s.subrange(1, s.len())),
  decreases s.len()
{
  if s.len() == 1 {
    assert(s[0] == '0');
    assert(str2int(s) == 0nat);
    assert(str2int(s.subrange(1, s.len())) == str2int(Seq::empty()) == 0nat);
  } else {
    lemma_str2int_leading_zero(s.subrange(1, s.len()));
  }
}

proof fn lemma_str2int_cons(c: char, s: Seq<char>)
  requires c == '0' || c == '1', valid_bit_string(s),
  ensures str2int(s.push(c)) == (if c == '1' { 1nat } else { 0nat }) + 2nat * str2int(s),
{
  let t = s.push(c);
  assert(t.len() == s.len() + 1);
  assert(t.subrange(0, t.len() - 1) == s);
  assert(t[t.len() - 1] == c);
}

spec fn carry_bit(c: int) -> bool {
  c >= 2
}

spec fn sum_bits(b1: char, b2: char, cin: bool) -> (int, bool)
  recommends b1 == '0' || b1 == '1', b2 == '0' || b2 == '1',
{
  let v1: int = if b1 == '1' { 1int } else { 0int };
  let v2: int = if b2 == '1' { 1int } else { 0int };
  let cin_val: int = if cin { 1int } else { 0int };
  let total = v1 + v2 + cin_val;
  (total % 2, total >= 2)
}

spec fn char_from_bit(b: int) -> char
  recommends b == 0 || b == 1,
{
  if b == 0 { '0' } else { '1' }
}

spec fn pow2(n: nat) -> nat
  decreases n
{
  if n == 0 {
    1nat
  } else {
    2nat * pow2((n - 1) as nat)
  }
}
// </vc-helpers>

// <vc-spec>
fn add(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
  ensures 
    valid_bit_string(res@),
    str2int(res@) == str2int(s1@) + str2int(s2@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed invariant syntax comma separator */
{
  let mut i = (s1.len() as isize) - 1;
  let mut j = (s2.len() as isize) - 1;
  let mut carry = false;
  let mut result = Vec::new();
  
  while i >= 0 || j >= 0 || carry
      invariant
          i >= -1 && j >= -1,
          (0i <= i) ==> (0 <= i as usize && i as usize < s1.len()),
          (0i <= j) ==> (0 <= j as usize && j as usize < s2.len()),
          valid_bit_string(result@)
      decreases 
          if i >= 0 { i } else { -1 } + 
          if j >= 0 { j } else { -1 } + 
          (if carry { 1 } else { 0 })
  {
    let b1 = if i >= 0 { s1[i as usize] } else { '0' };
    let b2 = if j >= 0 { s2[j as usize] } else { '0' };
    
    let (sum_b, new_carry) = sum_bits(b1, b2, carry);
    result.push(char_from_bit(sum_b));
    
    i = if i >= 0 { i - 1 } else { -1 };
    j = if j >= 0 { j - 1 } else { -1 };
    carry = new_carry;
  }
  
  result.reverse();
  
  let mut k: usize = 0;
  while k < result.len() && result[k] == '0'
      invariant
          0 <= k <= result.len()
      decreases result.len() - k
  {
    k += 1;
  }
  
  if k == result.len() {
    vec!['0']
  } else {
    let mut final_result = Vec::new();
    for idx in k..result.len() {
      final_result.push(result[idx]);
    }
    final_result
  }
}
// </vc-code>


}

fn main() {}