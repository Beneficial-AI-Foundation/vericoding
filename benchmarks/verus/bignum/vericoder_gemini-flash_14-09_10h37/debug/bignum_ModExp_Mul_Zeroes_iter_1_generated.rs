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
spec fn log2(n: nat) -> nat {
    if n <= 1 { 0 }
    else { 1 + log2(n / 2) }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let sy_seq = sy@;
    let sz_int = Str2Int(sz@);
    proof {
        if sy_seq.len() == 1 {
            if sy_seq.index(0) == '0' {
                assert(Str2Int(sy_seq) == 0);
                assert(Exp_int(Str2Int(sx@), 0) == 1);
            } else {
                assert(Str2Int(sy_seq) == 1);
                assert(Exp_int(Str2Int(sx@), 1) == Str2Int(sx@));
            }
        }
    }

    if sy_seq.len() == 1 {
        if sy_seq.index(0) == '0' {
            // sy = 0, result is 1 % sz
            let one_char = ['1'].to_vec();
            let one_seq = one_char@;
            if sz_int > 1 {
                assert(Str2Int(one_seq) % sz_int == 1 % sz_int);
                one_char
            } else {
                // This case should not be reachable due to the sz > 1 invariant
                // However, for completeness, if sz is 1, any mod 1 is 0
                let zero_char = ['0'].to_vec();
                zero_char
            }
        } else {
            // sy = 1, result is sx % sz
            let sx_val = Str2Int(sx@);
            let mod_res = sx_val % sz_int;
            let mut res_chars: Vec<char> = Vec::new();
            let radix = 2; // Binary representation
            if mod_res == 0 {
                res_chars.push('0');
            } else {
                let mut temp_mod_res = mod_res;
                while temp_mod_res > 0 {
                    if temp_mod_res % radix == 1 {
                        res_chars.push('1');
                    } else {
                        res_chars.push('0');
                    }
                    temp_mod_res = temp_mod_res / radix;
                }
                res_chars.reverse();
            }
            res_chars
        }
    } else {
        let sy_half = sy_seq.subrange(0, (sy_seq.len() as int - 1) as nat);
        let sy_last_bit = sy_seq.index((sy_seq.len() as int - 1) as nat);
        let sy_half_vec = sy_half.to_vec();

        let mut sx_chars_vec = sx.to_vec();

        // Recursive call for Exp_int(sx, sy / 2)
        let res_half_vec = ModExp_Mul_Zeroes(sx_chars_vec.as_slice(), sy_half_vec.as_slice(), sz);
        let res_half_seq = res_half_vec@;
        let res_half_val = Str2Int(res_half_seq);

        // Calculate (res_half_val * res_half_val) % sz_int
        let mut sq_val = (res_half_val * res_half_val) % sz_int;

        if sy_last_bit == '1' {
            // If sy is odd, multiply by sx one more time
            let sx_val = Str2Int(sx@);
            sq_val = (sq_val * sx_val) % sz_int;
        }

        // Convert sq_val back to a bit string
        let mut final_res_chars: Vec<char> = Vec::new();
        let radix = 2; // Binary representation

        if sq_val == 0 {
            final_res_chars.push('0');
        } else {
            let mut temp_sq_val = sq_val;
            while temp_sq_val > 0 {
                if temp_sq_val % radix == 1 {
                    final_res_chars.push('1');
                } else {
                    final_res_chars.push('0');
                }
                temp_sq_val = temp_sq_val / radix;
            }
            final_res_chars.reverse();
        }
        final_res_chars
    }
}
// </vc-code>

fn main() {}
}
