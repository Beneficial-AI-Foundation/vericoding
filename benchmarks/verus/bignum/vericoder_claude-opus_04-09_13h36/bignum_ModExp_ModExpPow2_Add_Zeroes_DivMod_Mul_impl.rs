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

spec fn Int2StrSpec(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 { seq!['0'] }
    else if n == 1 { seq!['1'] }
    else {
        let prefix = Int2StrSpec((n / 2) as nat);
        if n % 2 == 0 { prefix.push('0') }
        else { prefix.push('1') }
    }
}

proof fn int2str_spec_valid(n: nat)
    ensures ValidBitString(Int2StrSpec(n)), Str2Int(Int2StrSpec(n)) == n
    decreases n
{
    if n == 0 || n == 1 {
    } else {
        int2str_spec_valid((n / 2) as nat);
        let prefix = Int2StrSpec((n / 2) as nat);
        let res = if n % 2 == 0 { prefix.push('0') } else { prefix.push('1') };
        assert(res.subrange(0, res.len() as int - 1) == prefix);
        assert(Str2Int(res) == 2 * Str2Int(res.subrange(0, res.len() as int - 1)) + last_bit(res));
        if n % 2 == 0 {
            assert(last_bit(res) == 0);
            assert(Str2Int(res) == 2 * (n / 2) + 0);
            assert(n % 2 == 0 ==> n == 2 * (n / 2));
        } else {
            assert(last_bit(res) == 1);
            assert(Str2Int(res) == 2 * (n / 2) + 1);
            assert(n % 2 == 1 ==> n == 2 * (n / 2) + 1);
        }
    }
}

exec fn Int2StrExec(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n as nat, res@ == Int2StrSpec(n as nat)
    decreases n
{
    if n == 0 {
        return vec!['0'];
    } else if n == 1 {
        return vec!['1'];
    } else {
        let prefix = Int2StrExec(n / 2);
        let mut res = prefix;
        if n % 2 == 0 {
            res.push('0');
        } else {
            res.push('1');
        }
        proof {
            assert(res@.subrange(0, res@.len() as int - 1) == prefix@);
            assert(prefix@ == Int2StrSpec((n / 2) as nat));
            assert(res@.subrange(0, res@.len() as int - 1) == Int2StrSpec((n / 2) as nat));
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
            assert(res@ == Int2StrSpec(n as nat));
        }
        return res;
    }
}

exec fn Str2IntExec(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), Str2Int(s@) < 0x10000000000000000
    ensures res as nat == Str2Int(s@)
    decreases s@.len()
{
    if s.len() == 0 {
        return 0;
    } else {
        let end = (s.len() - 1) as usize;
        let mut prefix = Vec::new();
        for i in 0..end
            invariant
                prefix@.len() == i as int,
                forall |j: int| 0 <= j && j < i as int ==> prefix@[j] == s@[j],
                ValidBitString(prefix@)
        {
            prefix.push(s[i]);
        }
        let prefix_val = Str2IntExec(&prefix);
        let last = if s[s.len()-1] == '1' { 1u64 } else { 0u64 };
        proof {
            assert(prefix@ == s@.subrange(0, end as int));
            assert(s@.subrange(0, s@.len() as int - 1) == s@.subrange(0, end as int));
        }
        return 2 * prefix_val + last;
    }
}

exec fn StrMulMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
    requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), Str2Int(sz@) > 0,
             Str2Int(sx@) < 0x10000000000000000, Str2Int(sy@) < 0x10000000000000000, Str2Int(sz@) < 0x10000000000000000
    ensures ValidBitString(res@), Str2Int(res@) == (Str2Int(sx@) * Str2Int(sy@)) % Str2Int(sz@)
{
    let x_val = Str2IntExec(sx);
    let y_val = Str2IntExec(sy);
    let z_val = Str2IntExec(sz);
    
    let x_mod = x_val % z_val;
    let y_mod = y_val % z_val;
    let product_mod = (x_mod * y_mod) % z_val;
    
    proof {
        assert(x_val as nat == Str2Int(sx@));
        assert(y_val as nat == Str2Int(sy@));
        assert(z_val as nat == Str2Int(sz@));
        assert((x_val as nat * y_val as nat) % z_val as nat == ((x_val as nat % z_val as nat) * (y_val as nat % z_val as nat)) % z_val as nat);
        assert(product_mod as nat == (Str2Int(sx@) * Str2Int(sy@)) % Str2Int(sz@));
    }
    
    return Int2StrExec(product_mod);
}

exec fn StrDivBy2(s: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s@), s@.len() > 0
    ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s@) / 2
{
    if s.len() == 1 {
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
    if sy.len() == 1 && sy[0] == '0' {
        proof {
            assert(sy@.len() == 1);
            assert(sy@.index(0int) == '0');
            assert(Str2Int(sy@) == 0);
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
            assert(Str2Int(sy@) % 2 == 0);
            assert(Str2Int(sy_half@) == Str2Int(sy@) / 2);
            assert(Str2Int(sx_squared_mod@) == (Str2Int(sx@) * Str2Int(sx@)) % Str2Int(sz@));
            exp_even_odd(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
            assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@) == Exp_int((Str2Int(sx@) * Str2Int(sx@)) % Str2Int(sz@), Str2Int(sy@) / 2) % Str2Int(sz@));
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
            assert(Str2Int(sy@) % 2 == 1);
            assert(Str2Int(sy_half@) == Str2Int(sy@) / 2);
            assert(Str2Int(sx_squared_mod@) == (Str2Int(sx@) * Str2Int(sx@)) % Str2Int(sz@));
            exp_even_odd(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
            assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@) == (Str2Int(sx@) * Exp_int((Str2Int(sx@) * Str2Int(sx@)) % Str2Int(sz@), Str2Int(sy@) / 2)) % Str2Int(sz@));
            assert(Str2Int(temp@) == Exp_int(Str2Int(sx_squared_mod@), Str2Int(sy_half@)) % Str2Int(sz@));
            assert(Str2Int(result@) == (Str2Int(sx@) * Str2Int(temp@)) % Str2Int(sz@));
        }
        return result;
    }
}
// </vc-code>

fn main() {}
}