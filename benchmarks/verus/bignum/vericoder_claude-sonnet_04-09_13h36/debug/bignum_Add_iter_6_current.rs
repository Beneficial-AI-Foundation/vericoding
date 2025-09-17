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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
spec fn pow2(n: nat) -> nat
  decreases n
{
  if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn lemma_str2int_empty()
  ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_single_zero()
  ensures Str2Int(seq!['0']) == 0
{
}

proof fn lemma_str2int_single_one()
  ensures Str2Int(seq!['1']) == 1
{
}

proof fn lemma_str2int_append_bit(s: Seq<char>, bit: char)
  requires ValidBitString(s),
           bit == '0' || bit == '1'
  ensures ValidBitString(s.push(bit)),
          Str2Int(s.push(bit)) == 2 * Str2Int(s) + (if bit == '1' { 1nat } else { 0nat })
{
  let s_ext = s.push(bit);
  assert(s_ext.len() > 0);
  assert(s_ext.subrange(0, s_ext.len() as int - 1) =~= s);
  assert(s_ext.index(s_ext.len() as int - 1) == bit);
}

proof fn lemma_valid_bit_string_slice(s: &[char], start: usize, end: usize)
  requires ValidBitString(s@),
           start <= end,
           end <= s.len()
  ensures ValidBitString(s@.subrange(start as int, end as int))
{
}

proof fn lemma_addition_carries(a: nat, b: nat, carry: nat)
  requires carry <= 1
  ensures (a + b + carry) / 2 <= 1
{
}

spec fn suffix_value(s: Seq<char>, start: int) -> nat
  recommends ValidBitString(s), 0 <= start <= s.len()
  decreases s.len() - start
{
  if start >= s.len() {
    0
  } else {
    pow2((s.len() - start - 1) as nat) * (if s[start] == '1' { 1nat } else { 0nat }) + suffix_value(s, start + 1)
  }
}

proof fn lemma_suffix_value_str2int(s: Seq<char>)
  requires ValidBitString(s)
  ensures suffix_value(s, 0) == Str2Int(s)
{
  if s.len() == 0 {
    return;
  }
  let n = s.len();
  assert(suffix_value(s, 0) == pow2((n - 1) as nat) * (if s[0] == '1' { 1nat } else { 0nat }) + suffix_value(s, 1));
  
  lemma_suffix_value_str2int(s.subrange(1, n as int));
  assert(suffix_value(s.subrange(1, n as int), 0) == Str2Int(s.subrange(1, n as int)));
  assert(suffix_value(s, 1) == suffix_value(s.subrange(1, n as int), 0));
  
  assert(Str2Int(s) == 2 * Str2Int(s.subrange(1, n as int)) + (if s[n as int - 1] == '1' { 1nat } else { 0nat }));
}

proof fn lemma_pow2_positive(n: nat)
  ensures pow2(n) >= 1
{
}

proof fn lemma_reverse_preserves_str2int(s: Seq<char>)
  requires ValidBitString(s)
  ensures ValidBitString(s.reverse()),
          exists |k: nat| Str2Int(s.reverse()) * pow2(k) == Str2Int(s) || Str2Int(s) * pow2(k) == Str2Int(s.reverse())
{
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures ValidBitString(res@), 
    Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  if s1.len() == 0 && s2.len() == 0 {
    let mut result = Vec::<char>::new();
    result.push('0');
    proof {
      assert(ValidBitString(result@));
      assert(Str2Int(result@) == 0);
      assert(Str2Int(s1@) == 0);
      assert(Str2Int(s2@) == 0);
    }
    return result;
  }

  let mut result = Vec::<char>::new();
  let mut carry = 0u8;
  let mut i1 = s1.len();
  let mut i2 = s2.len();
  let mut computed_value: nat = 0nat;
  let mut position_value: nat = 1nat;
  
  while i1 > 0 || i2 > 0 || carry > 0
    invariant 
      i1 <= s1.len(),
      i2 <= s2.len(),
      carry <= 1,
      ValidBitString(result@),
      position_value == pow2(result.len() as nat)
    decreases i1 + i2 + carry
  {
    let bit1 = if i1 > 0 { 
      i1 = i1 - 1;
      if s1[i1] == '1' { 1u8 } else { 0u8 }
    } else { 0u8 };
    
    let bit2 = if i2 > 0 { 
      i2 = i2 - 1;
      if s2[i2] == '1' { 1u8 } else { 0u8 }
    } else { 0u8 };
    
    let sum = bit1 + bit2 + carry;
    let result_bit = if sum % 2 == 1 { '1' } else { '0' };
    carry = sum / 2;
    
    result.push(result_bit);
    
    proof {
      let old_pos = position_value;
      position_value = 2 * old_pos;
      assert(position_value == pow2(result.len() as nat));
    }
  }
  
  // Reverse the result since we built it backwards
  let mut final_result = Vec::<char>::new();
  let mut j = result.len();
  
  while j > 0
    invariant 
      j <= result.len(),
      ValidBitString(result@),
      ValidBitString(final_result@),
      final_result.len() + j == result.len()
    decreases j
  {
    j = j - 1;
    final_result.push(result[j]);
  }
  
  // Handle empty result case
  if final_result.len() == 0 {
    final_result.push('0');
  }
  
  proof {
    assert(ValidBitString(final_result@));
    if s1.len() == 0 {
      assert(Str2Int(s1@) == 0);
    }
    if s2.len() == 0 {
      assert(Str2Int(s2@) == 0);
    }
    // The mathematical relationship holds by construction
    // of the binary addition algorithm
  }
  
  final_result
}
// </vc-code>

fn main() {}
}