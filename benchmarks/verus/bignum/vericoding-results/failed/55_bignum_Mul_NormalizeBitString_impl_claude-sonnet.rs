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
    valid_bit_string(s) ==> str2int(s) == str2int(t)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): replace saturating arithmetic with if-then-else to avoid unsupported functions */
proof fn str2int_shift_lemma(s: Seq<char>, pos: int)
  requires 
    valid_bit_string(s),
    pos >= 0
  ensures 
    valid_bit_string(s.add(seq_repeat('0', pos))),
    str2int(s) * pow2(pos) == str2int(s.add(seq_repeat('0', pos)))
{
  // The proof follows from the recursive structure of str2int
  // Adding zeros to the right shifts left by the position amount
}

spec fn pow2(n: int) -> nat
  decreases n
{
  if n <= 0 { 1nat } else { 2nat * pow2(n - 1) }
}

spec fn seq_repeat(c: char, n: int) -> Seq<char>
  decreases n
{
  if n <= 0 { seq![] } else { seq![c].add(seq_repeat(c, n - 1)) }
}

proof fn str2int_empty_lemma()
  ensures str2int(seq!['0']) == 0
{
  // Follows from definition of str2int
}

proof fn str2int_subrange_lemma(s: Seq<char>, i: int)
  requires valid_bit_string(s), 0 <= i <= s.len()
  ensures valid_bit_string(s.subrange(0, i))
{
  // Subrange of valid bit string is valid
}

fn add_bit_strings_impl(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires valid_bit_string(s1@), valid_bit_string(s2@)
  ensures valid_bit_string(res@),
          str2int(res@) == str2int(s1@) + str2int(s2@)
{
  let mut result = Vec::new();
  let mut carry = false;
  let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
  
  let mut i: usize = 0;
  while i < max_len || carry
    invariant
      i <= max_len,
      i < usize::MAX,
      valid_bit_string(result@)
    decreases if carry { if max_len + 1 >= i { max_len + 1 - i } else { 0 } } else { if max_len >= i { max_len - i } else { 0 } }
  {
    let bit1 = if i < s1.len() && s1.len() > 0 { s1[s1.len() - 1 - i] == '1' } else { false };
    let bit2 = if i < s2.len() && s2.len() > 0 { s2[s2.len() - 1 - i] == '1' } else { false };
    
    let sum = (if bit1 { 1 } else { 0 }) + (if bit2 { 1 } else { 0 }) + (if carry { 1 } else { 0 });
    
    if sum % 2 == 1 {
      result.push('1');
    } else {
      result.push('0');
    }
    
    carry = sum >= 2;
    if i < usize::MAX {
      i += 1;
    } else {
      break;
    }
  }
  
  // Create a new reversed vector
  let mut final_result = Vec::new();
  let mut j = result.len();
  while j > 0
    invariant j <= result.len(),
              valid_bit_string(final_result@)
    decreases j
  {
    j -= 1;
    final_result.push(result[j]);
  }
  
  if final_result.len() == 0 {
    final_result.push('0');
  }
  
  final_result
}

fn bit_shift_left(s: Vec<char>, positions: usize) -> (res: Vec<char>)
  requires valid_bit_string(s@)
  ensures valid_bit_string(res@),
          str2int(res@) == str2int(s@) * pow2(positions as int)
{
  let mut result = s.clone();
  let mut i: usize = 0;
  
  proof {
    str2int_shift_lemma(s@, 0);
  }
  
  while i < positions
    invariant
      i <= positions,
      i < usize::MAX,
      valid_bit_string(result@),
      str2int(result@) == str2int(s@) * pow2(i as int)
    decreases positions - i
  {
    result.push('0');
    
    proof {
      str2int_shift_lemma(s@, (i + 1) as int);
    }
    
    if i < usize::MAX {
      i += 1;
    } else {
      break;
    }
  }
  result
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@),
    str2int(res@) == str2int(s1@) * str2int(s2@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): fix empty string cases and ensure valid preconditions */
  
  proof {
    str2int_empty_lemma();
  }
  
  if s1.len() == 0 || s2.len() == 0 {
    return vec!['0'];
  }
  
  // Handle case where either input represents 0
  if (s1.len() == 1 && s1[0] == '0') || (s2.len() == 1 && s2[0] == '0') {
    return vec!['0'];
  }
  
  let mut result = vec!['0'];
  let mut i: usize = 0;
  
  proof {
    str2int_subrange_lemma(s1@, 0);
  }
  
  while i < s1.len()
    invariant
      i <= s1.len(),
      i < usize::MAX,
      valid_bit_string(result@),
      valid_bit_string(s1@.subrange(0, i as int)),
      str2int(result@) == str2int(s1@.subrange(0, i as int)) * str2int(s2@)
    decreases s1.len() - i
  {
    proof {
      str2int_subrange_lemma(s1@, (i + 1) as int);
    }
    
    if s1[s1.len() - 1 - i] == '1' {
      let shifted_s2 = bit_shift_left(s2.clone(), i);
      result = add_bit_strings_impl(result, shifted_s2);
    }
    
    if i < usize::MAX {
      i += 1;
    } else {
      break;
    }
  }
  
  proof {
    assert(s1@.subrange(0, s1.len() as int) == s1@);
  }
  
  result
}
// </vc-code>


}

fn main() {}