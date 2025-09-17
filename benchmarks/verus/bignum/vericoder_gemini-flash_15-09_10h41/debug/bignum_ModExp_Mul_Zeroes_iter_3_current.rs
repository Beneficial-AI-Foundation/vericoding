use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
decreases y
{
    if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
recommends ValidBitString(s)
decreases s.len()
{
    if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
    forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed unnecessary lemmas */
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed type errors related to `nat` and `int` and `Vec::from_seq` to `Vec::from` */
{
    let sx_seq = sx@;
    let sy_seq = sy@;
    let sz_seq = sz@;

    let sy_len = sy_seq.len();
    if (sy_len as nat) == 0 { // Cast to nat for comparison
        let mut res = Vec::new();
        res.push('1');
        return res;
    } else if (sy_len as nat) == 1 { // Cast to nat for comparison
        if sy_seq.index(0int) == '0' { // explicit int index
            let mut res = Vec::new();
            res.push('1');
            return res;
        } else {
            return Vec::from(sx);
        }
    }

    let half_sy_len_int: int = sy_len / 2;
    let sy_half_1_seq = sy_seq.subrange(0, half_sy_len_int);
    let sy_half_2_seq = sy_seq.subrange(half_sy_len_int, sy_len as int); // Cast to int for subrange

    let r1_vec = ModExp_Mul_Zeroes(sx, &Vec::from(sy_half_1_seq), sz); // Changed from_seq to from
    let r2_vec = ModExp_Mul_Zeroes(sx, &Vec::from(sy_half_2_seq), sz); // Changed from_seq to from

    let r1 = r1_vec@;
    let r2 = r2_vec@;

    let modulus = Str2Int(sz_seq);
    let r1_val = Str2Int(r1);
    let r2_val = Str2Int(r2);

    let prod_val: nat;
    proof {
        prod_val = (r1_val * r2_val) % modulus;
    }

    let mut bit_string: Vec<char> = Vec::new();
    let mut temp_prod: nat = prod_val;

    if (temp_prod as nat) == 0 { // Cast to nat
        bit_string.push('0');
    } else {
        while (temp_prod as nat) > 0 // Cast to nat
            invariant
                ValidBitString(bit_string@),
            decreases temp_prod
        {
            let rem: nat;
            let next_temp_prod: nat;
            proof {
                rem = temp_prod % 2;
                next_temp_prod = temp_prod / 2;
            }
            if (rem as nat) == 1 { // Cast to nat
                bit_string.push('1');
            } else {
                bit_string.push('0');
            }
            temp_prod = next_temp_prod;
        }
    }

    bit_string.reverse();
    return bit_string;
}
// </vc-code>

fn main() {}
}
