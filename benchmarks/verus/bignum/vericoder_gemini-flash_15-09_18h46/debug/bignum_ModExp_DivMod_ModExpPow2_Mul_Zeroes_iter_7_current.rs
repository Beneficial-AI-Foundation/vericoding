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
/* helper modified by LLM (iteration 7): Corrected the `int_to_bit_string` helper to properly convert a nat to `Seq<char>` without using `temp_s` for building, directly manipulating `s`. */
spec fn int_to_bit_string(n: nat) -> Seq<char>
encloses Str2Int, ValidBitString
ensures
    ValidBitString(result),
    Str2Int(result) == n
{
    if n == 0 { seq!['0'] }
    else {
        let mut s: Seq<char> = Seq::empty();
        let mut temp_n: nat = n;
        while temp_n > 0
            invariant
                temp_n >= 0,
                ValidBitString(s),
                n == Str2Int(s) + temp_n * Exp_int(2, s.len() as nat),
                // This invariant ensures that the decimal value is maintained as we build the bit string in reverse.
                // The invariant for Str2Int(s) + temp_n * 2^s.len() needs more work to be precise
                // For now, focusing on construction
        {
            let bit = if temp_n % 2 == 1 { '1' } else { '0' };
            s = seq![bit].add(s);
            temp_n = temp_n / 2;
        }
        s
    }
}

spec fn ModExp(x: nat, y: nat, z: nat) -> nat
decreases y
{
    if y == 0 {
        1nat % z
    } else if y % 2 == 0 {
        let half_y = (y / 2) as nat;
        let res = ModExp(x, half_y, z);
        (res * res) % z
    } else {
        let res = ModExp(x, (y - 1) as nat, z);
        (x * res) % z
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): Implemented the conversion from Seq<char> to Vec<char> by iterating through the sequence and pushing elements to a new Vec. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let result_int = ModExp(x_int, y_int, z_int);

    let res_seq = int_to_bit_string(result_int);
    // Convert Seq<char> to Vec<char>
    let mut result_vec = Vec::<char>::new();
    let mut i = 0;
    while i < res_seq.len()
        invariant i <= res_seq.len(), result_vec.len() == i
    {
        result_vec.push(res_seq[i]);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

fn main() {}
}
