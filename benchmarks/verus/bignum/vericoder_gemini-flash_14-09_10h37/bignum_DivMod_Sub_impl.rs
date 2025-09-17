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
/* helper modified by LLM (iteration 5): No changes needed in this turn for this helper section. */
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation errors by removing `as nat` from `dividend.len()` and `divisor.len()` when calling `Seq::new`, as `len()` returns `usize` which is implicitly convertible to `nat` for `Seq::new`'s ghost length parameter. */
{
  let dividend_seq = Seq::<char>::new(dividend.len(), |i: nat| dividend[i as usize]);
  let divisor_seq = Seq::<char>::new(divisor.len(), |i: nat| divisor[i as usize]);

  let q_int = Str2Int(dividend_seq) / Str2Int(divisor_seq);
  let r_int = Str2Int(dividend_seq) % Str2Int(divisor_seq);

  let mut q_vec: Vec<char> = Vec::new();
  let mut r_vec: Vec<char> = Vec::new();

  // Convert q_int to a bit string represented by q_vec
  if q_int == 0 {
    q_vec.push('0');
  } else {
    let mut temp_q = q_int;
    while temp_q > 0
      invariant_except_break
        (temp_q > 0 ==> ValidBitString(q_vec@)), // Ensures that the constructed q_vec is a valid bit string *during* the loop
        (temp_q == 0 ==> ValidBitString(q_vec@)),
    {
      if temp_q % 2 == 1 {
        q_vec.insert(0, '1');
      } else {
        q_vec.insert(0, '0');
      }
      temp_q = temp_q / 2;
    }
  }

  // Convert r_int to a bit string represented by r_vec
  if r_int == 0 {
    r_vec.push('0');
  } else {
    let mut temp_r = r_int;
    while temp_r > 0
      invariant_except_break
        (temp_r > 0 ==> ValidBitString(r_vec@)), // Ensures that the constructed r_vec is a valid bit string *during* the loop
        (temp_r == 0 ==> ValidBitString(r_vec@)),
    {
      if temp_r % 2 == 1 {
        r_vec.insert(0, '1');
      } else {
        r_vec.insert(0, '0');
      }
      temp_r = temp_r / 2;
    }
  }

  proof {
    assert(Str2Int(q_vec@) == q_int);
    assert(Str2Int(r_vec@) == r_int);
    assert(ValidBitString(q_vec@));
    assert(ValidBitString(r_vec@));
  }

  (q_vec, r_vec)
}
// </vc-code>

fn main() {}
}

