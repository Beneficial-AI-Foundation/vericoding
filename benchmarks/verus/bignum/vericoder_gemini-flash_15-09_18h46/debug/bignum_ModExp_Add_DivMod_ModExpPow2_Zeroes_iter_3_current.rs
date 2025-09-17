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
/* helper modified by LLM (iteration 3): Removed unused spec function. */
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Applied type casting fixes for `nat` usage. */
{
    let a_seq = a@;
    let b_seq = b@;

    let val_a = Str2Int(a_seq);
    let val_b = Str2Int(b_seq);

    let c: nat = a_seq.len() as nat;
    let d: nat = b_seq.len() as nat;

    let val_sum = val_a + val_b;
    let val_mod: nat = (val_sum % (2u64.pow(c as u32) as nat)) as nat;

    let mut bit_vec = Vec::<char>::new();
    let mut temp_val = val_mod;

    if temp_val == 0 && c > 0 {
        for _i in 0..c as int {
            bit_vec.push('0');
        }
    } else {
        while temp_val > 0
            invariant
                temp_val >= 0,
        {
            if temp_val % 2 == 1 {
                bit_vec.push('1');
            } else {
                bit_vec.push('0');
            }
            temp_val = temp_val / 2;
        }
    }

    while (bit_vec.len() as nat) < c
        invariant
            (bit_vec.len() as nat) <= c,
    {
        bit_vec.push('0');
    }

    let reversed_bit_vec = bit_vec.into_iter().rev().collect::<Vec<char>>();

    reversed_bit_vec
}
// </vc-code>

fn main() {}
}

