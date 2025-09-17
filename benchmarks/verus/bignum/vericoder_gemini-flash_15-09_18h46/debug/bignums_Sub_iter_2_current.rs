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
/* helper modified by LLM (iteration 2): Fixing return signature for SubHelper */
spec fn SubHelper(s1: Seq<char>, s2: Seq<char>, carry: nat) -> (res: Seq<char>, next_carry: nat)
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixing an issue with empty result from SubHelper when both inputs are 0. */
{
  let s1_seq = s1@;
  let s2_seq = s2@;

  let max_len = if s1_seq.len() >= s2_seq.len() { s1_seq.len() } else { s2_seq.len() };

  let s1_padded = pad_left_zeros(s1_seq, max_len);
  let s2_padded = pad_left_zeros(s2_seq, max_len);

  proof {
    remove_leading_zeros_preserves_validity(s1_seq);
    remove_leading_zeros_preserves_validity(s2_seq);
    assert(ValidBitString(s1_padded));
    assert(ValidBitString(s2_padded));

    // Prove that padding doesn't change the value if it's not all zeros
    if s1_seq.len() > 0 && Str2Int(s1_seq) > 0 {
      Str2Int_padding_left_zeros(s1_seq, max_len);
    }
    if s2_seq.len() > 0 && Str2Int(s2_seq) > 0 {
      Str2Int_padding_left_zeros(s2_seq, max_len);
    }
    
    // Handle the case where one of the original numbers is 0, Str2Int_padding_left_zeros requires > 0
    if Str2Int(s1_seq) == 0 && max_len > 0 {
        assert(Str2Int(s1_padded) == 0);
    }
    if Str2Int(s2_seq) == 0 && max_len > 0 {
        assert(Str2Int(s2_padded) == 0);
    }

    assert(Str2Int(s1_padded) == Str2Int(s1_seq));
    assert(Str2Int(s2_padded) == Str2Int(s2_seq));

    if max_len > 0 {
      SubHelper_relates_Str2Int(s1_padded, s2_padded, 0);
    } else {
      assert(Str2Int(Seq::empty()) == 0);
    }
  }

  // if both numbers are empty or '0', result is '0'
  if Str2Int(s1_seq) == 0 && Str2Int(s2_seq) == 0 {
      let mut res_vec = Vec::new();
      res_vec.push('0');
      return res_vec;
  }

  let (mut res_seq, _next_carry) = SubHelper(s1_padded, s2_padded, 0);

  proof {
    assert(_next_carry == 0);
    assert(Str2Int(res_seq) == Str2Int(s1_seq) - Str2Int(s2_seq));
    remove_leading_zeros_preserves_validity(res_seq);
  }

  res_seq = remove_leading_zeros(res_seq);

  let mut res_vec = Vec::new();
  res_vec.reserve(res_seq.len());
  let mut i = 0;
  while i < res_seq.len()
    invariant
      0 <= i && i <= res_seq.len(),
      res_vec.len() == i,
      forall |j: int| 0 <= j && j < i ==> res_vec[j] == res_seq.index(j),
  {
    res_vec.push(res_seq.index(i));
    i = i + 1;
  }
  res_vec
}
// </vc-code>

fn main() {}
}


