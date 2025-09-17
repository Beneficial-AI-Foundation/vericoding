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
spec fn last_bit(s: Seq<char>) -> nat
    recommends s.len() > 0
{
    if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }
}

proof fn str2int_decompose(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + last_bit(s)
{
}

exec fn Int2Str(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
    decreases n
{
    if n == 0nat {
        return vec!['0'];
    } else if n == 1nat {
        return vec!['1'];
    } else {
        let mut res = Int2Str((n / 2) as nat);
        if n % 2 == 0nat {
            res.push('0');
        } else {
            res.push('1');
        }
        proof {
            assert(res@.subrange(0, res@.len() as int - 1) == Int2Str((n / 2) as nat)@);
            assert(Str2Int(res@) == 2 * Str2Int(res@.subrange(0, res@.len() as int - 1)) + last_bit(res@));
            if n % 2 == 0 {
                assert(last_bit(res@) == 0);
                assert(Str2Int(res@) == 2 * (n / 2) + 0);
                assert(n % 2 == 0 ==> n == 2 * (n / 2));
            } else {
                assert(last_bit(res@) == 1);
                assert(Str2Int(res@) == 2 * (n / 2) + 1);
                assert(n % 2 == 1 ==> n == 2 * (n / 2) + 1);
            }
        }
        return res;
    }
}

exec fn StrMulMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
    requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), Str2Int(sz@) > 0
    ensures ValidBitString(res@), Str2Int(res@) == (Str2Int(sx@) * Str2Int(sy@)) % Str2Int(sz@)
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    let x_mod = x_val % z_val;
    let y_mod = y_val % z_val;
    let product_mod = (x_mod * y_mod) % z_val;
    
    proof {
        assert((x_val * y_val) % z_val == ((x_val % z_val) * (y_val % z_val)) % z_val);
    }
    
    return Int2Str(product_mod);
}

exec fn StrDivBy2(s: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s@), s@.len() > 0
    ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s@) / 2
{
    if s@.len() == 1nat {
        return vec!['0'];
    } else {
        let mut res = Vec::new();
        for i in 0..(s.len() - 1) {
            res.push(s[i]);
        }
        proof {
            assert(res@ == s@.subrange(0, s@.len() as int - 1));
            str2int_decompose(s@);
            assert(Str2Int(s@) == 2 * Str2Int(s@.subrange(0, s@.len() as int - 1)) + last_bit(s@));
            assert(Str2Int(s@) / 2 == Str2Int(s@.subrange(0, s@.len() as int - 1)));
        }
        return res;
    }
}

proof fn exp_recursive(x: nat, y: nat)
    requires y > 0
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
}

proof fn exp_even_odd(x: nat, y: nat, z: nat)
    requires y > 0, z > 1
    ensures 
        y % 2 == 0 ==> Exp_int(x, y) % z == Exp_int((x * x) % z, y / 2) % z,
        y % 2 == 1 ==> Exp_int(x, y) % z == (x * Exp_int((x * x) % z, y / 2)) % z
{
    if y % 2 == 0 {
        assert(y == 2 * (y / 2));
        assert(Exp_int(x, y) == Exp_int(x * x, y / 2));
    } else {
        assert(y == 2 * (y / 2) + 1);
        assert(Exp_int(x, y) == x * Exp_int(x * x, y / 2));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Add_Zeroes_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let y_val = Str2Int(sy@);
    
    if sy@.len() == 1nat && sy@.index(0) == '0' {
        proof {
            assert(y_val == 0);
            assert(Exp_int(Str2Int(sx@), 0) == 1);
        }
        return vec!['1'];
    }
    
    let last_char = sy[sy.len() - 1];
    
    if last_char == '0' {
        // y is even
        let sy_half = StrDivBy2(sy);
        let sx_squared_mod = StrMulMod(sx, sx, sz);
        let result = ModExp_ModExpPow2_Add_Zeroes_DivMod_Mul(&sx_squared_mod, &sy_half, sz);
        
        proof {
            assert(sy@.index(sy@.len() as int - 1) == '0');
            assert(y_val % 2 == 0);
            assert(Str2Int(sy_half@) == y_val / 2);
            assert(Str2Int(sx_squared_mod@) == (Str2Int(sx@) * Str2Int(sx@)) % Str2Int(sz@));
            exp_even_odd(Str2Int(sx@), y_val, Str2Int(sz@));
            assert(Exp_int(Str2Int(sx@), y_val) % Str2Int(sz@) == Exp_int((Str2Int(sx@) * Str2Int(sx@)) % Str2Int(sz@), y_val / 2) % Str2Int(sz@));
            assert(Str2Int(result@) == Exp_int(Str2Int(sx_squared_mod@), Str2Int(sy_half@)) % Str2Int(sz@));
        }
        return result;
    } else {
        // y is odd
        let sy_half = StrDivBy2(sy);
        let sx_squared_mod = StrMulMod(sx, sx, sz);
        let temp = ModExp_ModExpPow2_Add_Zeroes_DivMod_Mul(&sx_squared_mod, &sy_half, sz);
        let result = StrMulMod(sx, &temp, sz);
        
        proof {
            assert(sy@.index(sy@.len() as int - 1) == '1');
            assert(y_val % 2 == 1);
            assert(Str2Int(sy_half@) == y_val / 2);
            assert(Str2Int(sx_squared_mod@) == (Str2Int(sx@) * Str2Int(sx@)) % Str2Int(sz@));
            exp_even_odd(Str2Int(sx@), y_val, Str2Int(sz@));
            assert(Exp_int(Str2Int(sx@), y_val) % Str2Int(sz@) == (Str2Int(sx@) * Exp_int((Str2Int(sx@) * Str2Int(sx@)) % Str2Int(sz@), y_val / 2)) % Str2Int(sz@));
            assert(Str2Int(temp@) == Exp_int(Str2Int(sx_squared_mod@), Str2Int(sy_half@)) % Str2Int(sz@));
            assert(Str2Int(result@) == (Str2Int(sx@) * Str2Int(temp@)) % Str2Int(sz@));
        }
        return result;
    }
}
// </vc-code>

fn main() {}
}