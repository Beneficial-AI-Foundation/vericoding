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
/* helper modified by LLM (iteration 4): (No fix needed, previously removed helper) */
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Cast ghost variables to u128 for arithmetic operations. */
{
    let a_seq = a@;
    let b_seq = b@;

    let val_a = Str2Int(a_seq);
    let val_b = Str2Int(b_seq);

    let c_int: int = a_seq.len();
    let d_int: int = b_seq.len();

    let val_sum = val_a + val_b;
    let val_mod: nat;

    // Check if c_int is non-negative before using it in pow
    if c_int >= 0 {
        let power_of_2: nat = (2u128.pow(c_int as u32)) as nat;
        val_mod = (val_sum % power_of_2) as nat;
    } else {
        // Handle error case for negative c_int. For now, setting to 0.
        // A more robust solution might involve Verus failing verification or returning an error.
        val_mod = 0;
    }

    let mut bit_vec = Vec::<char>::new();
    let mut temp_val = val_mod;

    if temp_val == 0 && c_int > 0 {
        for _i in 0..c_int {
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

    let mut bit_vec_len: int = bit_vec.len();
    while bit_vec_len < c_int
        invariant
            bit_vec_len <= c_int,
    {
        bit_vec.push('0');
        bit_vec_len = bit_vec_len + 1;
    }

    let reversed_bit_vec = bit_vec.into_iter().rev().collect::<Vec<char>>();

    reversed_bit_vec
}
// </vc-code>

fn main() {}
}

