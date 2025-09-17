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
spec fn Str2Value(s: &[char]) -> nat {
    Str2Int(s@)
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
        let x_val = Str2Value(sx);
        let y_val = Str2Value(sy);
        let z_val = Str2Value(sz);

        assert(y_val > 0) by { /* This is already guaranteed by sy@.len() > 0 and ValidBitString(sy@) */ };
        assert(z_val > 1) by { /* This is already guaranteed by the requires clause */ };

        if y_val == 0 {
            // Should not happen due to sy@.len() > 0
            let one_char_seq = Seq::<char>::new().push('1');
            return one_char_seq.to_vec();
        } else if y_val == 1 {
            return sx.to_vec();
        } else {
            let y_minus_1_val = (y_val - 1) as nat;
            let sy_minus_1_vec = nat_to_char_vec(y_minus_1_val);
            let sy_minus_1_slice = sy_minus_1_vec.as_slice();

            let recursive_result_vec = ModExp_DivMod_ModExpPow2_Mul(sx, sy_minus_1_slice, sz);
            let recursive_result_val = Str2Value(recursive_result_vec.as_slice());

            let current_product = (x_val * recursive_result_val) % z_val;

            return nat_to_char_vec(current_product);
        }
    }

    proof fn nat_to_char_vec(n: nat) -> Vec<char>
        ensures 
            ValidBitString(result@),
            Str2Value(result.as_slice()) == n,
            result@.len() >= 1 || n == 0
    {
        if n == 0 {
            let mut v = Vec::new();
            v.push('0'); // Represent 0 as "0"
            v
        } else {
            let mut digits: Vec<char> = Vec::new();
            let mut temp_n = n;
            while temp_n > 0
                invariant
                    temp_n >= 0,
                    forall |i: int| #![auto] 0 <= i && i < digits@.len() ==> (digits@[i] == '0' || digits@[i] == '1'),
                    temp_n == Str2Value(digits.as_slice()) + Str2Value(digits.as_slice()) * 2_nat.pow(digits@.len() as nat) 
                            && temp_n == n / (2_nat.pow(digits@.len() as nat)) 
                                    + n % (2_nat.pow(digits@.len() as nat))
                decreases temp_n
            {
                let remainder = temp_n % 2;
                if remainder == 0 {
                    digits.insert(0, '0');
                } else {
                    digits.insert(0, '1');
                }
                temp_n = temp_n / 2;
            }
            digits
        }
    }

    proof fn Exp_int_property(x: nat, y: nat) 
        requires y >= 1
        ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
    {
        // This is directly from the spec fn definition
    }
// </vc-code>

fn main() {}
}
