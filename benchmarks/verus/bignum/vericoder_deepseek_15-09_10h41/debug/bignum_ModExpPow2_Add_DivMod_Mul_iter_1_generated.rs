
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
proof fn Str2Int_nonnegative(s: Seq<char>) 
  requires ValidBitString(s)
  ensures Str2Int(s) >= 0
  decreases s.len()
{
  if s.len() == 0 {
  } else {
    Str2Int_nonnegative(s.subrange(0, s.len() as int - 1));
  }
}

proof fn Str2Int_monotonic(s: Seq<char>, t: Seq<char>) 
  requires ValidBitString(s), ValidBitString(t), s.len() <= t.len()
  ensures Str2Int(s) <= Str2Int(t)
  decreases s.len(), t.len()
{
  if s.len() == 0 {
  } else {
    Str2Int_monotonic(s.subrange(0, s.len() as int - 1), t.subrange(0, t.len() as int - 1));
  }
}

proof fn BitString_length_positive(s: Seq<char>) 
  requires ValidBitString(s), s.len() > 0
  ensures s@[s.len() as int - 1] == '0' || s@[s.len() as int - 1] == '1'
{
}

proof fn Str2Int_append(s: Seq<char>, bit: char) 
  requires ValidBitString(s), bit == '0' || bit == '1'
  ensures Str2Int(s.push(bit)) == 2 * Str2Int(s) + (if bit == '1' {1} else {0})
  decreases s.len()
{
  if s.len() == 0 {
  } else {
    Str2Int_append(s.subrange(0, s.len() as int - 1), s@[s.len() as int - 1]);
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_Add_DivMod_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
  let mut result = Vec::new();
  let mut power_seq = a.to_owned();
  let length_helper = vstd::seq::new_seq(0, b.len() as int, |i| b@[i]);

  proof {
    Str2Int_nonnegative(a@);
    if b.len() > 0 { BitString_length_positive(b@); }
  }

  for i in 0..b.len()
      invariant ValidBitString(result@), ValidBitString(power_seq@)
      invariant BinaryBitStringValidLengthInvariant(result, power_seq, b, i)
      decreases b.len() - i
  {
    if b[i] == '1' {
      result = append_bit_strings(&result, &power_seq);
      proof { BinaryAdditionPreservesValidity(result@, power_seq@); }
    }
    
    if i < b.len() - 1 {
      power_seq = multiply_by_two(&power_seq);
      proof { BinaryMultiplicationPreservesValidity(power_seq@); }
    }
  }
  
  result
}
// </vc-code>

fn main() {}
}

