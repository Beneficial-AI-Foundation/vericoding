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

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut seen_one = false;
    if s.len() == 0 {
        result.push('0');
        return result;
    }
    for i in 0..s.len() {
        let char_val = s[i];
        if char_val == '1' {
            seen_one = true;
            result.push(char_val);
        } else if char_val == '0' {
            if seen_one {
                result.push(char_val);
            }
        }
    }
    if !seen_one || result.is_empty() {
        result.push('0');
    }
    result
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed push_front as it does not exist on Seq. */
spec fn ReverseSeq<T: core::marker::Copy>(s: Seq<T>) -> Seq<T>
{
  if s.len() == 0 {
    Seq::<T>::empty()
  } else {
    let first_element = s.index(0);
    let tail_rev = ReverseSeq(s.subrange(1, s.len()));
    tail_rev.push(first_element)
  }
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
/* code modified by LLM (iteration 2): Fixed type mismatches (int to nat) and issues with using Vec::push_front. */
{
  let s1_len = s1.len();
  let s2_len = s2.len();
  let max_len = if s1_len > s2_len { s1_len } else { s2_len };
  
  let mut result_vec_rev: Vec<char> = Vec::new();
  let mut carry: nat = 0nat;
  let mut j: nat = 0nat;

  while j < max_len as nat || carry == 1nat
    invariant
      j <= max_len as nat + 1,
      carry == 0nat || carry == 1nat,
  {
    let mut bit1: nat = 0nat;
    if (j < s1_len as nat) {
      if (s1[s1_len - 1 - j as int] == '1') {
        bit1 = 1nat;
      }
    }

    let mut bit2: nat = 0nat;
    if (j < s2_len as nat) {
      if (s2[s2_len - 1 - j as int] == '1') {
        bit2 = 1nat;
      }
    }

    let sum = bit1 + bit2 + carry;

    if (sum % 2nat == 1nat) {
      result_vec_rev.push('1');
    } else {
      result_vec_rev.push('0');
    }

    carry = sum / 2nat;
    j = j + 1nat;
  }
  
  let mut result: Vec<char> = Vec::new();
  let mut k = result_vec_rev.len() as int - 1;
  while k >= 0
    invariant
      k >= -1,
      k < result_vec_rev.len(),
      result.len() == result_vec_rev.len() as int - 1 - k,
  {
      result.push(result_vec_rev[k as usize]);
      k = k - 1;
  }

  NormalizeBitString(&result)
}
// </vc-code>

fn main() {}
}


