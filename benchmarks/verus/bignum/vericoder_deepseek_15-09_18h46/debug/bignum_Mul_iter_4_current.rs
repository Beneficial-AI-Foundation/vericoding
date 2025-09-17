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
/* helper modified by LLM (iteration 4): Fix max function to be spec mode and rename to avoid conflict */
spec fn spec_max(a: int, b: int) -> int { if a > b { a } else { b } }

proof fn lemma_max_properties(a: int, b: int)
  ensures spec_max(a, b) >= a && spec_max(a, b) >= b,
          spec_max(a, b) == a || spec_max(a, b) == b
{
}

proof fn lemma_str2int_recursive(s: Seq<char>)
  requires ValidBitString(s), s.len() > 0
  ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
{
}

proof fn lemma_str2int_zero()
  ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_nonnegative(s: Seq<char>)
  requires ValidBitString(s)
  ensures Str2Int(s) >= 0
{
}

proof fn lemma_str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
  requires ValidBitString(s1), ValidBitString(s2), s1.len() <= s2.len()
  ensures Str2Int(s1) <= Str2Int(s2)
{
}

proof fn lemma_str2int_append_zero(s: Seq<char>)
  requires ValidBitString(s)
  ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
{
}

proof fn lemma_str2int_append_one(s: Seq<char>)
  requires ValidBitString(s)
  ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
}

proof fn lemma_mul_distributive(a: nat, b: nat, c: nat)
  ensures a * (b + c) == a * b + a * c
{
}

proof fn lemma_mul_associative(a: nat, b: nat, c: nat)
  ensures a * (b * c) == (a * b) * c
{
}

proof fn lemma_mul_commutative(a: nat, b: nat)
  ensures a * b == b * a
{
}

proof fn lemma_mul_zero(a: nat)
  ensures a * 0 == 0
{
}

proof fn lemma_mul_one(a: nat)
  ensures a * 1 == a
{
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fix compilation error by removing call to max function */
{
  let mut result = Vec::<char>::new();
  let n1 = s1.len();
  let n2 = s2.len();
  
  for i in 0..n1 {
    let mut partial = Vec::<char>::new();
    
    for _ in 0..i {
      partial.push('0');
    }
    
    let carry = if s1[i] == '1' {
      let mut current_carry = 0;
      
      for j in 0..n2 {
        let bit1 = if s2[j] == '1' { 1 } else { 0 };
        let sum = bit1 + current_carry;
        partial.push(if sum % 2 == 1 { '1' } else { '0' });
        current_carry = sum / 2;
      }
      
      if current_carry > 0 {
        partial.push('1');
      }
      
      current_carry
    } else {
      0
    };
    
    let mut new_result = Vec::<char>::new();
    let mut carry_result = 0;
    let max_len = if result.len() > partial.len() { result.len() } else { partial.len() };
    
    for k in 0..max_len {
      let bit_result = if k < result.len() && result[k] == '1' { 1 } else { 0 };
      let bit_partial = if k < partial.len() && partial[k] == '1' { 1 } else { 0 };
      let sum = bit_result + bit_partial + carry_result;
      new_result.push(if sum % 2 == 1 { '1' } else { '0' });
      carry_result = sum / 2;
    }
    
    if carry_result > 0 {
      new_result.push('1');
    }
    
    result = new_result;
  }
  
  result
}
// </vc-code>

fn main() {}
}


