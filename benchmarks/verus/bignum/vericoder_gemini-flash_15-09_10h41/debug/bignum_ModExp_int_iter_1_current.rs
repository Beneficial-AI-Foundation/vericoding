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
spec fn SeqToNat(s: Seq<char>) -> nat {
    Str2Int(s)
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_int = SeqToNat(sx@);
    let y_int = SeqToNat(sy@);
    let z_int = SeqToNat(sz@);

    if y_int == 0 {
        let mut res: Vec<char> = Vec::new();
        res.push('1');
        return res;
    } else if y_int == 1 {
        let res_val = x_int % z_int;
        return nat_to_bit_string(res_val);
    } else {
        let y_minus_1_seq = nat_to_bit_string(y_int - 1);
        let mut recurse_result = ModExp_int(sx, &y_minus_1_seq.view(), sz);
        let recurse_int = SeqToNat(recurse_result@);
        let final_val = (x_int * recurse_int) % z_int;
        return nat_to_bit_string(final_val);
    }
}

// Placeholder for nat_to_bit_string function needed in the above implementation
fn nat_to_bit_string(n: nat) -> (s: Vec<char>)
    ensures ValidBitString(s@), SeqToNat(s@) == n
{
    if n == 0 {
        let mut res = Vec::new();
        res.push('0');
        return res;
    } else {
        let mut res: Vec<char> = Vec::new();
        let mut current_n = n;
        while current_n > 0
            invariant
                current_n >= 0,
            decreases current_n
        {
            if current_n % 2 == 1 {
                res.insert(0, '1');
            } else {
                res.insert(0, '0');
            }
            current_n = current_n / 2;
        }
        return res;
    }
}
// </vc-code>

fn main() {}
}
