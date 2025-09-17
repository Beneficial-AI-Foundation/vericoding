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
spec fn shift_left(s: Seq<char>, n: nat) -> Seq<char>
  recommends ValidBitString(s)
{
  s + seq!['0'; n]
}

proof fn lemma_remove_leading_zeros_preserves_str2int(s: Seq<char>, start: int)
  requires ValidBitString(s), 0 <= start <= s.len()
  requires forall |j: int| 0 <= j < start ==> s[j] == '0'
  ensures Str2Int(s) == Str2Int(s.subrange(start, s.len() as int))
  decreases start
{
  if start == 0 {
  } else if s.len() == 0 {
  } else {
    assert(s[start - 1] == '0');
    lemma_remove_leading_zeros_preserves_str2int(s, start - 1);
    assert(Str2Int(s) == Str2Int(s.subrange(start - 1, s.len() as int)));
    let s_sub = s.subrange(start - 1, s.len() as int);
    assert(s_sub.len() > 0);
    assert(s_sub[0] == '0');
    assert(Str2Int(s_sub) == 2 * Str2Int(s_sub.subrange(0, s_sub.len() - 1)) + 0);
    assert(s_sub.subrange(1, s_sub.len() as int) == s.subrange(start, s.len() as int));
  }
}

proof fn lemma_str2int_zero_string(s: Seq<char>)
  requires ValidBitString(s)
  requires forall |i: int| 0 <= i < s.len() ==> s[i] == '0'
  ensures Str2Int(s) == 0
  decreases s.len()
{
  if s.len() == 0 {
  } else {
    lemma_str2int_zero_string(s.subrange(0, s.len() - 1));
  }
}

proof fn lemma_shift_left_str2int(s: Seq<char>, n: nat)
  requires ValidBitString(s)
  ensures Str2Int(shift_left(s, n)) == Str2Int(s) * pow(2, n)
  decreases s.len()
{
  if s.len() == 0 {
    lemma_str2int_zero_string(seq!['0'; n]);
  } else {
    let shifted = shift_left(s, n);
    let s_prefix = s.subrange(0, s.len() - 1);
    let last_bit = s[s.len() - 1];
    
    lemma_shift_left_str2int(s_prefix, n);
    
    assert(Str2Int(shifted) == 2 * Str2Int(shifted.subrange(0, shifted.len() - 1)) + 
           (if shifted[shifted.len() - 1] == '1' { 1nat } else { 0nat }));
    assert(shifted[shifted.len() - 1] == '0');
    assert(shifted.subrange(0, shifted.len() - 1) == shift_left(s, n - 1));
  }
}

proof fn lemma_multiplication_decomposition(s1: Seq<char>, s2: Seq<char>, i: nat)
  requires ValidBitString(s1), ValidBitString(s2)
  requires i < s2.len()
  ensures Str2Int(s1) * (if s2[s2.len() - 1 - i] == '1' { pow(2, i) } else { 0 }) ==
          (if s2[s2.len() - 1 - i] == '1' { Str2Int(s1) * pow(2, i) } else { 0 })
{
}

exec fn remove_leading_zeros(s: &Vec<char>) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s@), res.len() >= 1
{
  let mut start = 0;
  while start < s.len() && s[start] == '0'
    invariant 0 <= start <= s.len(), ValidBitString(s@)
    invariant forall |j: int| 0 <= j < start ==> s@[j] == '0'
    decreases s.len() - start
  {
    start += 1;
  }
  
  if start == s.len() {
    proof {
      lemma_str2int_zero_string(s@);
    }
    vec!['0']
  } else {
    let mut result = Vec::new();
    let mut i = start;
    while i < s.len()
      invariant start <= i <= s.len(), ValidBitString(s@), ValidBitString(result@)
      invariant result@ == s@.subrange(start as int, i as int)
      decreases s.len() - i
    {
      result.push(s[i]);
      i += 1;
    }
    proof {
      lemma_remove_leading_zeros_preserves_str2int(s@, start as int);
      assert(result@ == s@.subrange(start as int, s.len() as int));
    }
    result
  }
}

exec fn reverse_vec(v: &Vec<char>) -> (res: Vec<char>)
  requires ValidBitString(v@)
  ensures ValidBitString(res@), res.len() == v.len()
{
  let mut result = Vec::new();
  let mut i = v.len();
  while i > 0
    invariant ValidBitString(v@), ValidBitString(result@), 
              i <= v.len(), result.len() == v.len() - i
    decreases i
  {
    i -= 1;
    result.push(v[i]);
  }
  result
}

exec fn add_binary_strings(s1: &Vec<char>, s2: &Vec<char>) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
{
  let mut result = Vec::new();
  let mut carry = 0u8;
  let mut i1 = s1.len();
  let mut i2 = s2.len();
  
  while i1 > 0 || i2 > 0 || carry > 0
    invariant ValidBitString(s1@), ValidBitString(s2@), ValidBitString(result@),
              i1 <= s1.len(), i2 <= s2.len(), carry <= 1
    decreases i1 + i2 + carry as usize
  {
    let bit1 = if i1 > 0 && s1[i1 - 1] == '1' { 1u8 } else { 0u8 };
    let bit2 = if i2 > 0 && s2[i2 - 1] == '1' { 1u8 } else { 0u8 };
    
    let sum = bit1 + bit2 + carry;
    result.push(if sum % 2 == 1 { '1' } else { '0' });
    carry = sum / 2;
    
    if i1 > 0 { i1 -= 1; }
    if i2 > 0 { i2 -= 1; }
  }
  
  let reversed = reverse_vec(&result);
  remove_leading_zeros(&reversed)
}

exec fn shift_left_binary(s: &Vec<char>, positions: usize) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s@) * pow(2, positions as nat)
{
  if s.len() == 1 && s[0] == '0' {
    vec!['0']
  } else {
    let mut result = s.clone();
    let mut i = 0;
    while i < positions
      invariant ValidBitString(result@)
      invariant result@ == s@ + seq!['0'; i]
      decreases positions - i
    {
      result.push('0');
      i += 1;
    }
    proof {
      lemma_shift_left_str2int(s@, positions as nat);
      assert(result@ == shift_left(s@, positions as nat));
    }
    result
  }
}

exec fn slice_to_vec(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@), res@ == s@
{
  let mut result = Vec::new();
  let mut i = 0;
  while i < s.len()
    invariant ValidBitString(s@), ValidBitString(result@),
              i <= s.len(), result@ == s@.subrange(0, i as int)
    decreases s.len() - i
  {
    result.push(s[i]);
    i += 1;
  }
  result
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  if s1.len() == 0 || s2.len() == 0 {
    proof {
      if s1.len() == 0 {
        assert(Str2Int(s1@) == 0);
      } else {
        assert(Str2Int(s2@) == 0);
      }
      assert(Str2Int(s1@) * Str2Int(s2@) == 0);
      assert(Str2Int(seq!['0']) == 0);
    }
    return vec!['0'];
  }
  
  if (s1.len() == 1 && s1[0] == '0') || (s2.len() == 1 && s2[0] == '0') {
    proof {
      if s1.len() == 1 && s1[0] == '0' {
        assert(Str2Int(s1@) == 0);
      } else {
        assert(Str2Int(s2@) == 0);
      }
      assert(Str2Int(s1@) * Str2Int(s2@) == 0);
      assert(Str2Int(seq!['0']) == 0);
    }
    return vec!['0'];
  }
  
  let mut result = vec!['0'];
  let mut i = 0;
  
  while i < s2.len()
    invariant ValidBitString(s1@), ValidBitString(s2@), ValidBitString(result@),
              i <= s2.len()
    decreases s2.len() - i
  {
    if s2[s2.len() - 1 - i] == '1' {
      let s1_vec = slice_to_vec(s1);
      let shifted = shift_left_binary(&s1_vec, i);
      result = add_binary_strings(&result, &shifted);
    }
    i += 1;
  }
  
  result
}
// </vc-code>

fn main() {}
}