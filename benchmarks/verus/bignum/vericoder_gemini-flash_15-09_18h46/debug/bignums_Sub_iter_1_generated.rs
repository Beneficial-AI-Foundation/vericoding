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
spec fn SubHelper(s1: Seq<char>, s2: Seq<char>, carry: nat) -> (res: Seq<char>, next_carry: nat)
  requires ValidBitString(s1), ValidBitString(s2),
           s1.len() == s2.len(),
           carry == 0 || carry == 1,
           Str2Int(s1) >= Str2Int(s2) + carry,
           s1.len() > 0
  ensures ValidBitString(res),
          next_carry == 0,
          Str2Int(res) + carry == Str2Int(s1) - Str2Int(s2)
  decreases s1.len()
{
  let s1_last = s1.index(s1.len() as int - 1);
  let s2_last = s2.index(s2.len() as int - 1);

  let d1 = if s1_last == '1' { 1nat } else { 0nat };
  let d2 = if s2_last == '1' { 1nat } else { 0nat };

  let diff = d1 as int - d2 as int - carry as int;

  let current_digit;
  let new_carry;

  if diff < 0 {
    current_digit = if diff + 2 == 1 { '1' } else { '0' };
    new_carry = 1;
    assert(d1 + 2 == d2 + carry + Str2Int(Seq::singleton(current_digit)))
  } else {
    current_digit = if diff == 1 { '1' } else { '0' };
    new_carry = 0;
    assert(d1 == d2 + carry + Str2Int(Seq::singleton(current_digit)))
  }

  if s1.len() == 1 {
    (Seq::singleton(current_digit), new_carry)
  } else {
    let (prev_res, prev_carry) = SubHelper(
      s1.subrange(0, s1.len() as int - 1),
      s2.subrange(0, s2.len() as int - 1),
      new_carry,
    );
    (prev_res + Seq::singleton(current_digit), prev_carry)
  }
}

spec fn remove_leading_zeros(s: Seq<char>) -> Seq<char>
  ensures (
    Str2Int(remove_leading_zeros(s)) == Str2Int(s)
  )
  decreases s.len()
{
  if s.len() <= 1 {
    s
  } else {
    if s.index(0) == '0' {
      let remaining = s.subrange(1, s.len() as int);
      if Str2Int(remaining) == 0 && s.index(0) == '0' {
         Seq::singleton('0') // Only one '0' for the value 0
      } else {
        remove_leading_zeros(remaining)
      }
    } else {
      s
    }
  }
}

lemma fn remove_leading_zeros_preserves_validity(s: Seq<char>) 
  requires ValidBitString(s)
  ensures ValidBitString(remove_leading_zeros(s))
  decreases s.len()
{
  if s.len() <= 1 {
    // Base case: already valid or empty
  } else {
    if s.index(0) == '0' {
      let remaining = s.subrange(1, s.len() as int);
      remove_leading_zeros_preserves_validity(remaining);
      if !(Str2Int(remaining) == 0 && s.index(0) == '0') {
        // if not special case ('0') then we know result is valid recursively
      }
    }
  }
}

lemma fn Str2Int_padding_left_zeros(s: Seq<char>, pad_len: int)
  requires ValidBitString(s),
           pad_len >= s.len() as int,
           Str2Int(s) > 0
  ensures Str2Int(pad_left_zeros(s, pad_len)) == Str2Int(s)
{
  if s.len() < pad_len {
    let padding_count = pad_len - s.len() as int;
    assert(Str2Int(Seq::fill(padding_count, |i| '0') + s) == Str2Int(s)) by {
      // Inductive step: Str2Int(new_prefix + s) == Str2Int(new_prefix) * 2^s.len() + Str2Int(s)
      // If new_prefix is all '0's, Str2Int(new_prefix) == 0
    }
  }
}

lemma fn SubHelper_relates_Str2Int(s1: Seq<char>, s2: Seq<char>, carry: nat)
  requires ValidBitString(s1), ValidBitString(s2),
           s1.len() == s2.len(),
           carry == 0 || carry == 1,
           Str2Int(s1) >= Str2Int(s2) + carry,
           s1.len() > 0
  ensures {
    let (res, next_carry) = SubHelper(s1, s2, carry);
    Str2Int(res) + (next_carry as nat) * (2_nat.pow(res.len())) == Str2Int(s1) - Str2Int(s2) + carry * (2_nat.pow(res.len()))
  }
  decreases s1.len()
{
  let s1_last = s1.index(s1.len() as int - 1);
  let s2_last = s2.index(s2.len() as int - 1);

  let d1 = if s1_last == '1' { 1nat } else { 0nat };
  let d2 = if s2_last == '1' { 1nat } else { 0nat };

  let diff = d1 as int - d2 as int - carry as int;

  let current_digit;
  let new_carry;

  if diff < 0 {
    current_digit = if diff + 2 == 1 { '1' } else { '0' };
    new_carry = 1;
  } else {
    current_digit = if diff == 1 { '1' } else { '0' };
    new_carry = 0;
  }

  if s1.len() == 1 {
    assert(Str2Int(Seq::singleton(current_digit)) == (d1 as nat) + 2*new_carry - (d2 as nat) - (carry as nat));
  } else {
    let (prev_res, prev_carry) = SubHelper(
      s1.subrange(0, s1.len() as int - 1),
      s2.subrange(0, s2.len() as int - 1),
      new_carry,
    );
    SubHelper_relates_Str2Int(
      s1.subrange(0, s1.len() as int - 1),
      s2.subrange(0, s2.len() as int - 1),
      new_carry,
    );

    let prev_s1 = s1.subrange(0, s1.len() as int - 1);
    let prev_s2 = s2.subrange(0, s2.len() as int - 1);

    assert(Str2Int(prev_res) + (prev_carry as nat) * (2_nat.pow(prev_res.len())) == 
           Str2Int(prev_s1) - Str2Int(prev_s2) + (new_carry as nat) * (2_nat.pow(prev_res.len())));

    // Verify the property for the concatenated result
    // Str2Int(res) = Str2Int(prev_res) * 2 + Str2Int(Seq::singleton(current_digit))
    // Str2Int(s1) = Str2Int(prev_s1) * 2 + d1
    // Str2Int(s2) = Str2Int(prev_s2) * 2 + d2
    // Goal: Str2Int(res) + (next_carry as nat) * (2_nat.pow(res.len())) == Str2Int(s1) - Str2Int(s2) + carry * (2_nat.pow(res.len()))

    let rhs_prev = Str2Int(prev_s1) - Str2Int(prev_s2) + (new_carry as nat) * (2_nat.pow(prev_res.len()));
    let lhs_prev = Str2Int(prev_res) + (prev_carry as nat) * (2_nat.pow(prev_res.len()));
    assert(lhs_prev == rhs_prev);

    assert(d1 as int - d2 as int - carry as int == Str2Int(Seq::singleton(current_digit)) as int - 2 * new_carry as int);
    assert(d1 as nat - d2 as nat - carry as nat == Str2Int(Seq::singleton(current_digit)) - 2*new_carry);

    assert(Str2Int(prev_res) * 2 + Str2Int(Seq::singleton(current_digit)) + (prev_carry as nat) * (2_nat.pow(prev_res.len() + 1)) ==
           (Str2Int(prev_s1) - Str2Int(prev_s2) + (new_carry as nat) * (2_nat.pow(prev_res.len()))) * 2 
           + Str2Int(Seq::singleton(current_digit)) 
           + (prev_carry as nat) * (2_nat.pow(prev_res.len() + 1)));

    assert(Str2Int(prev_res) * 2 + Str2Int(Seq::singleton(current_digit)) + (prev_carry as nat) * (2_nat.pow(prev_res.len() + 1)) ==
           Str2Int(prev_s1) * 2 + d1 - (Str2Int(prev_s2) * 2 + d2) - carry * (2_nat.pow(res.len())) + carry * (2_nat.pow(res.len()))
          );
  }
}


spec fn pad_left_zeros(s: Seq<char>, target_len: int) -> Seq<char>
  requires s.len() as int <= target_len
  ensures ValidBitString(pad_left_zeros(s, target_len))
  ensures pad_left_zeros(s, target_len).len() == target_len
{
  let diff = (target_len - s.len() as int);
  Seq::fill(diff, |i| '0') + s
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
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
      assert(Str2Int(S2::empty()) == 0);
    }

  }

  // if both numbers are empty or '0', result is '0'
  if max_len == 0 {
      return Vec::new();
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


