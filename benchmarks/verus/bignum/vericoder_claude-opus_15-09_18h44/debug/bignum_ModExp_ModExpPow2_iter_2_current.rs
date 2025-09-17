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
spec fn mod_nat(a: nat, b: nat) -> nat
    recommends b > 0
{
    a % b
}

proof fn exp_mod_property(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures exp > 0 ==> Exp_int(base, exp) % modulus == ((base % modulus) * (Exp_int(base, (exp - 1) as nat) % modulus)) % modulus
    decreases exp
{
    if exp > 0 {
        reveal(Exp_int);
        assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
    }
}

exec fn Int2Str(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@),
        Str2Int(res@) == n
    decreases n
{
    if n == 0 {
        vec!['0']
    } else if n == 1 {
        vec!['1']
    } else {
        let mut res = Int2Str(n / 2);
        if n % 2 == 0 {
            res.push('0');
        } else {
            res.push('1');
        }
        proof {
            reveal(Str2Int);
            assert(res@.len() > 0);
            let s = res@;
            assert(s.subrange(0, s.len() as int - 1) == Int2Str(n / 2)@);
            if n % 2 == 0 {
                assert(s.index(s.len() as int - 1) == '0');
                assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + 0);
            } else {
                assert(s.index(s.len() as int - 1) == '1');
                assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + 1);
            }
            assert(Str2Int(s) == 2 * (n / 2) + n % 2);
            assert(2 * (n / 2) + n % 2 == n);
        }
        res
    }
}

exec fn ModMul(x: nat, y: nat, z: nat) -> (res: nat)
    requires z > 1
    ensures res == (x * y) % z
{
    ((x % z) * (y % z)) % z
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed type casting issues in exec code */
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);
    
    if sy@.len() == 1 {
        if sy@.index(0) == '0' {
            proof {
                reveal(Str2Int);
                assert(y == 0);
                reveal(Exp_int);
                assert(Exp_int(x, 0) == 1);
            }
            return Int2Str(1 % z);
        } else {
            proof {
                reveal(Str2Int);
                assert(sy@.index(0) == '1');
                assert(y == 1);
                reveal(Exp_int);
                assert(Exp_int(x, 1) == x * Exp_int(x, 0));
                assert(Exp_int(x, 0) == 1);
                assert(Exp_int(x, 1) == x);
            }
            return Int2Str(x % z);
        }
    }
    
    let sy_prefix = &sy[0..(sy.len() - 1)];
    proof {
        assert(sy_prefix@.len() == sy@.len() - 1);
        assert(forall |i: int| 0 <= i && i < sy_prefix@.len() as int ==> sy_prefix@.index(i) == sy@.index(i));
        assert(ValidBitString(sy_prefix@));
    }
    
    let half_exp_result = ModExp_ModExpPow2(sx, sy_prefix, sz);
    let half_exp_val = Str2Int(half_exp_result@);
    
    let squared = ModMul(half_exp_val, half_exp_val, z);
    
    let last_bit = sy@.index((sy@.len() - 1) as int);
    let result = if last_bit == '1' {
        ModMul(squared, x, z)
    } else {
        squared
    };
    
    proof {
        let y_prefix = Str2Int(sy_prefix@);
        reveal(Str2Int);
        assert(sy@.subrange(0, sy@.len() as int - 1) == sy_prefix@);
        
        if last_bit == '1' {
            assert(y == 2 * y_prefix + 1);
            reveal(Exp_int);
            assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
            assert((y - 1) as nat == 2 * y_prefix);
            assert(Exp_int(x, 2 * y_prefix) == Exp_int(x, y_prefix) * Exp_int(x, y_prefix)) by {
                reveal(Exp_int);
                if y_prefix > 0 {
                    assert(Exp_int(x, 2 * y_prefix) == x * Exp_int(x, (2 * y_prefix - 1) as nat));
                }
            }
            assert(half_exp_val == Exp_int(x, y_prefix) % z);
            assert(squared == (Exp_int(x, y_prefix) * Exp_int(x, y_prefix)) % z);
            assert(result == ((Exp_int(x, y_prefix) * Exp_int(x, y_prefix)) % z * x) % z);
            exp_mod_property(x, y, z as nat);
        } else {
            assert(y == 2 * y_prefix);
            assert(Exp_int(x, y) == Exp_int(x, y_prefix) * Exp_int(x, y_prefix)) by {
                reveal(Exp_int);
                if y_prefix > 0 {
                    assert(Exp_int(x, 2 * y_prefix) == x * Exp_int(x, (2 * y_prefix - 1) as nat));
                }
            }
            assert(half_exp_val == Exp_int(x, y_prefix) % z);
            assert(result == (Exp_int(x, y_prefix) * Exp_int(x, y_prefix)) % z);
        }
        
        assert(result == Exp_int(x, y) % z);
    }
    
    Int2Str(result)
}
// </vc-code>

fn main() {}
}
