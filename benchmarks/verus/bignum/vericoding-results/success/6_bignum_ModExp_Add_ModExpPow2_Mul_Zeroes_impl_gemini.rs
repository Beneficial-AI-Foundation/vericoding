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
proof fn lemma_valid_bit_string_concat(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
    ensures
        ValidBitString(s1 + s2),
{

}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    let mut res = Vec::new();
    res.extend_from_slice(a);
    res.extend_from_slice(b);

    proof {
        lemma_valid_bit_string_concat(a@, b@);
        assert(res@ == a@ + b@);
    }

    res
}
// </vc-code>

fn main() {}
}

