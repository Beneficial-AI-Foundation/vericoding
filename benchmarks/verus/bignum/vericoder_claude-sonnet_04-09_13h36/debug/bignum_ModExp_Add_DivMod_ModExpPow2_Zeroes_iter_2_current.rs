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
proof fn empty_seq_valid_bitstring()
  ensures ValidBitString(Seq::<char>::empty())
{
  let empty_seq = Seq::<char>::empty();
  assert(empty_seq.len() == 0);
  assert(forall |i: int| 0 <= i && i < empty_seq.len() as int ==> 
    (empty_seq.index(i) == '0' || empty_seq.index(i) == '1'));
}

proof fn single_zero_valid_bitstring()
  ensures ValidBitString(vec!['0']@)
{
  let v = vec!['0'];
  assert(v@.len() == 1);
  assert(v@.index(0) == '0');
  assert(forall |i: int| 0 <= i && i < v@.len() as int ==> 
    (v@.index(i) == '0' || v@.index(i) == '1'));
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
  proof {
    single_zero_valid_bitstring();
  }
  vec!['0']
}
// </vc-code>

fn main() {}
}