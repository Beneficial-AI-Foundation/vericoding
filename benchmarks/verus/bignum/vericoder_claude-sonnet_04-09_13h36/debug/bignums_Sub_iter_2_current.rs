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
spec fn pad_zeros(s: Seq<char>, len: nat) -> Seq<char>
{
  if s.len() >= len {
    s
  } else {
    seq!['0'; len - s.len()] + s
  }
}

proof fn lemma_pad_zeros_preserves_value(s: Seq<char>, len: nat)
  requires ValidBitString(s)
  ensures ValidBitString(pad_zeros(s, len))
  ensures Str2Int(pad_zeros(s, len)) == Str2Int(s)
{
  if s.len() >= len {
    assert(pad_zeros(s, len) == s);
  } else {
    let zeros = seq!['0'; len - s.len()];
    let padded = zeros + s;
    assert(padded == pad_zeros(s, len));
    
    lemma_leading_zeros_preserve_value(zeros, s);
  }
}

proof fn lemma_leading_zeros_preserve_value(zeros: Seq<char>, s: Seq<char>)
  requires forall |i: int| 0 <= i < zeros.len() ==> zeros[i] == '0'
  requires ValidBitString(s)
  ensures ValidBitString(zeros + s)
  ensures Str2Int(zeros + s) == Str2Int(s)
  decreases zeros.len()
{
  if zeros.len() == 0 {
    assert(zeros + s == s);
  } else {
    let tail = zeros.subrange(1, zeros.len() as int);
    lemma_leading_zeros_preserve_value(tail, s);
    assert((zeros + s).subrange(0, (zeros + s).len() as int - 1) == zeros + s.subrange(0, s.len() as int - 1));
  }
}

exec fn binary_subtract_same_length(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires s1.len() == s2.len()
  requires ValidBitString(s1@)
  requires ValidBitString(s2@)
  requires Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@)
  ensures Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
{
  let mut result = Vec::new();
  let mut borrow = false;
  let len = s1.len();
  
  let mut i = len;
  while i > 0
    invariant
      0 <= i <= len,
      ValidBitString(result@),
      result.len() == len - i,
      forall |j: int| 0 <= j < result.len() ==> (result@[j] == '0' || result@[j] == '1')
  {
    i -= 1;
    let bit1 = s1[i];
    let bit2 = s2[i];
    
    let (diff, new_borrow) = if borrow {
      if bit1 >= bit2 {
        if bit1 == '1' && bit2 == '0' {
          ('0', false)
        } else {
          ('1', true)
        }
      } else {
        ('1', true)
      }
    } else {
      if bit1 >= bit2 {
        (if bit1 == bit2 { '0' } else { '1' }, false)
      } else {
        ('1', true)
      }
    };
    
    result.push(diff);
    borrow = new_borrow;
  }
  
  result.reverse();
  result
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  let len1 = s1.len();
  let len2 = s2.len();
  let max_len = if len1 > len2 { len1 } else { len2 };
  
  if max_len == 0 {
    return Vec::new();
  }
  
  let mut padded_s1 = Vec::new();
  let mut padded_s2 = Vec::new();
  
  // Pad s1 with leading zeros
  let mut i = 0;
  while i < max_len - len1 {
    padded_s1.push('0');
    i += 1;
  }
  i = 0;
  while i < len1 {
    padded_s1.push(s1[i]);
    i += 1;
  }
  
  // Pad s2 with leading zeros
  i = 0;
  while i < max_len - len2 {
    padded_s2.push('0');
    i += 1;
  }
  i = 0;
  while i < len2 {
    padded_s2.push(s2[i]);
    i += 1;
  }
  
  proof {
    lemma_pad_zeros_preserves_value(s1@, max_len);
    lemma_pad_zeros_preserves_value(s2@, max_len);
  }
  
  let result = binary_subtract_same_length(&padded_s1, &padded_s2);
  
  // Remove leading zeros
  let mut start = 0;
  while start < result.len() && result[start] == '0' {
    start += 1;
  }
  
  if start == result.len() {
    let mut final_result = Vec::new();
    final_result.push('0');
    return final_result;
  }
  
  let mut final_result = Vec::new();
  i = start;
  while i < result.len() {
    final_result.push(result[i]);
    i += 1;
  }
  
  final_result
}
// </vc-code>

fn main() {}
}