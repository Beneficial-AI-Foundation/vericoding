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
proof fn helper_lemma(x: nat, y: nat) requires y > 0 ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat) { }

proof fn str2int_recursive_lemma(s: Seq<char>) requires ValidBitString(s), s.len() > 0 ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) { }

proof fn mod_exp_lemma(base: nat, exp: nat, modulus: nat) requires modulus > 1 ensures Exp_int(base, exp) % modulus == (base * Exp_int(base, (exp - 1) as nat)) % modulus { }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let m = *sz;
    let m_int = Str2Int(m@);
    
    if sy@.len() == 1 {
        let base_val = Str2Int(sx@);
        let exp_val = Str2Int(sy@);
        let result_val = Exp_int(base_val, exp_val) % m_int;
        let mut result_vec = Vec::new();
        while result_val > 0 {
            if result_val % 2 == 1 {
                result_vec.push('1');
            } else {
                result_vec.push('0');
            }
            result_val = result_val / 2;
        }
        result_vec.reverse();
        if result_vec.is_empty() {
            result_vec.push('0');
        }
        result_vec
    } else {
        let base_val = Str2Int(sx@);
        let exp_first_bit = if sy@[0] == '1' { 1 } else { 0 };
        let exp_remaining = sy@.subrange(1, sy@.len() as int);
        let intermediate = Exp_int(base_val, Str2Int(exp_remaining) as nat) % m_int;
        let final_val = (Exp_int(base_val, exp_first_bit) * intermediate) % m_int;
        
        proof { helper_lemma(base_val, Str2Int(sy@) as nat); }
        
        let mut result_vec = Vec::new();
        let mut current = final_val;
        while current > 0 {
            if current % 2 == 1 {
                result_vec.push('1');
            } else {
                result_vec.push('0');
            }
            current = current / 2;
        }
        result_vec.reverse();
        if result_vec.is_empty() {
            result_vec.push('0');
        }
        result_vec
    }
}
// </vc-code>

fn main() {}
}
