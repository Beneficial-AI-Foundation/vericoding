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
/* helper modified by LLM (iteration 9): Add decreases clause to lemma_str2int_monotonic */
proof fn lemma_str2int_zero()
  ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_nonnegative(s: Seq<char>)
  requires ValidBitString(s)
  ensures Str2Int(s) >= 0
{
}

proof fn lemma_str2int_recursive(s: Seq<char>)
  requires ValidBitString(s), s.len() > 0
  ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
{
}

proof fn lemma_str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
  requires ValidBitString(s1), ValidBitString(s2), s1.len() <= s2.len()
  ensures Str2Int(s1) <= Str2Int(s2)
  decreases s1.len() + s2.len()
{
  if s1.len() == 0 {
    lemma_str2int_zero();
    lemma_str2int_nonnegative(s2);
  } else {
    let s1_prefix = s1.subrange(0, s1.len() as int - 1);
    let s2_prefix = s2.subrange(0, s2.len() as int - 1);
    lemma_str2int_monotonic(s1_prefix, s2_prefix);
    let last_bit1: nat = if s1.index(s1.len() as int - 1) == '1' { 1nat } else { 0nat };
    let last_bit2: nat = if s2.index(s2.len() as int - 1) == '1' { 1nat } else { 0nat };
    lemma_str2int_recursive(s1);
    lemma_str2int_recursive(s2);
  }
}

proof fn lemma_str2int_append_zero(s: Seq<char>)
  requires ValidBitString(s)
  ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
{
  lemma_str2int_recursive(s.push('0'));
  assert(s.push('0').len() == s.len() + 1);
  assert(s.push('0').index(s.len() as int) == '0');
}

proof fn lemma_str2int_append_one(s: Seq<char>)
  requires ValidBitString(s)
  ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
  lemma_str2int_recursive(s.push('1'));
  assert(s.push('1').len() == s.len() + 1);
  assert(s.push('1').index(s.len() as int) == '1');
}

proof fn lemma_mul_distributive(a: nat, b: nat, c: nat)
  ensures a * (b + c) == a * b + a * c
{
  if a == 0 {
  } else {
    lemma_mul_distributive((a - 1) as nat, b, c);
  }
}

proof fn lemma_mul_associative(a: nat, b: nat, c: nat)
  ensures a * (b * c) == (a * b) * c
{
  if a == 0 {
  } else {
    lemma_mul_associative((a - 1) as nat, b, c);
  }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): Add proper type annotations and fix compilation errors */
{
  let mut result = Vec::<char>::new();
  let n1 = s1.len();
  let n2 = s2.len();
  
  for i in 0..n1 {
    let mut partial = Vec::<char>::new();
    
    for _ in 0..i {
      partial.push('0');
    }
    
    let carry: i32 = if s1[i] == '1' {
      let mut current_carry = 0;
      
      for j in 0..n2 {
        let bit1: i32 = if s2[j] == '1' { 1 } else { 0 };
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
      let bit_result: i32 = if k < result.len() && result[k] == '1' { 1 } else { 0 };
      let bit_partial: i32 = if k < partial.len() && partial[k] == '1' { 1 } else { 0 };
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


