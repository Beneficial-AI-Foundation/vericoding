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
/* helper modified by LLM (iteration 8): fixed type annotations for nat literals */
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

exec fn Int2Str(n: u64) -> (res: Vec<char>)
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

exec fn ModMul(x: u64, y: u64, z: u64) -> (res: u64)
    requires z > 1
    ensures res == ((x as int) * (y as int)) % (z as int)
{
    ((x % z) * (y % z)) % z
}

exec fn Str2Int_exec(s: &[char]) -> (res: u64)
    requires ValidBitString(s@),
        s@.len() <= 64,
        Str2Int(s@) < u64::MAX
    ensures res == Str2Int(s@)
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let prefix = &s[0..(s.len() - 1)];
        proof {
            assert(prefix@ == s@.subrange(0, s@.len() as int - 1));
            assert(ValidBitString(prefix@));
        }
        let prefix_val = Str2Int_exec(prefix);
        let last_bit = if s[s.len() - 1] == '1' { 1u64 } else { 0u64 };
        proof {
            reveal(Str2Int);
            assert(Str2Int(s@) == 2 * Str2Int(prefix@) + (if s@.index(s@.len() as int - 1) == '1' { 1nat } else { 0nat }));
        }
        2 * prefix_val + last_bit
    }
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
    /* code modified by LLM (iteration 8): fixed type annotations and sequence indexing */
    proof {
        assert(sx@.len() >= 0);
        assert(sy@.len() >= 1);
        assert(sz@.len() >= 0);
    }
    
    if sy@.len() == 1nat {
        if sy@.index(0int) == '0' {
            proof {
                reveal(Str2Int);
                assert(Str2Int(sy@) == 0);
                reveal(Exp_int);
                assert(Exp_int(Str2Int(sx@), 0) == 1);
            }
            let z_val = Str2Int_exec(sz);
            proof { assert(z_val > 1); }
            return Int2Str(1 % z_val);
        } else {
            proof {
                reveal(Str2Int);
                assert(sy@.index(0 as int) == '1');
                assert(Str2Int(sy@) == 1);
                reveal(Exp_int);
                assert(Exp_int(Str2Int(sx@), 1) == Str2Int(sx@) * Exp_int(Str2Int(sx@), 0));
                assert(Exp_int(Str2Int(sx@), 0) == 1);
                assert(Exp_int(Str2Int(sx@), 1) == Str2Int(sx@));
            }
            let x_val = Str2Int_exec(sx);
            let z_val = Str2Int_exec(sz);
            proof { assert(z_val > 1); }
            return Int2Str(x_val % z_val);
        }
    }
    
    let sy_prefix = &sy[0..(sy.len() - 1)];
    proof {
        assert(sy_prefix@.len() == sy@.len() - 1);
        assert(forall |i: int| 0 <= i && i < sy_prefix@.len() as int ==> sy_prefix@.index(i) == sy@.index(i));
        assert(ValidBitString(sy_prefix@));
    }
    
    let half_exp_result = ModExp_ModExpPow2(sx, sy_prefix, sz);
    let half_exp_val = Str2Int_exec(&half_exp_result);
    
    let x_val = Str2Int_exec(sx);
    let z_val = Str2Int_exec(sz);
    
    let squared = ModMul(half_exp_val, half_exp_val, z_val);
    
    let last_bit = sy[sy.len() - 1];
    let result = if last_bit == '1' {
        ModMul(squared, x_val, z_val)
    } else {
        squared
    };
    
    proof {
        assert(last_bit == sy@.index((sy@.len() - 1) as int));
        let y_prefix = Str2Int(sy_prefix@);
        reveal(Str2Int);
        assert(sy@.subrange(0, sy@.len() as int - 1) == sy_prefix@);
        
        if last_bit == '1' {
            assert(Str2Int(sy@) == 2 * y_prefix + 1);
            reveal(Exp_int);
            assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) == Str2Int(sx@) * Exp_int(Str2Int(sx@), (Str2Int(sy@) - 1) as nat));
            assert((Str2Int(sy@) - 1) as nat == 2 * y_prefix);
            assert(Exp_int(Str2Int(sx@), 2 * y_prefix) == Exp_int(Str2Int(sx@), y_prefix) * Exp_int(Str2Int(sx@), y_prefix)) by {
                reveal(Exp_int);
                if y_prefix > 0 {
                    assert(Exp_int(Str2Int(sx@), 2 * y_prefix) == Str2Int(sx@) * Exp_int(Str2Int(sx@), (2 * y_prefix - 1) as nat));
                }
            };
            assert(half_exp_val == Exp_int(Str2Int(sx@), y_prefix) % Str2Int(sz@));
            assert(squared == (Exp_int(Str2Int(sx@), y_prefix) * Exp_int(Str2Int(sx@), y_prefix)) % Str2Int(sz@));
            assert(result == ((Exp_int(Str2Int(sx@), y_prefix) * Exp_int(Str2Int(sx@), y_prefix)) % Str2Int(sz@) * Str2Int(sx@)) % Str2Int(sz@));
            exp_mod_property(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
        } else {
            assert(Str2Int(sy@) == 2 * y_prefix);
            assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) == Exp_int(Str2Int(sx@), y_prefix) * Exp_int(Str2Int(sx@), y_prefix)) by {
                reveal(Exp_int);
                if y_prefix > 0 {
                    assert(Exp_int(Str2Int(sx@), 2 * y_prefix) == Str2Int(sx@) * Exp_int(Str2Int(sx@), (2 * y_prefix - 1) as nat));
                }
            };
            assert(half_exp_val == Exp_int(Str2Int(sx@), y_prefix) % Str2Int(sz@));
            assert(result == (Exp_int(Str2Int(sx@), y_prefix) * Exp_int(Str2Int(sx@), y_prefix)) % Str2Int(sz@));
        }
        
        assert(result == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    Int2Str(result)
}
// </vc-code>

fn main() {}
}
