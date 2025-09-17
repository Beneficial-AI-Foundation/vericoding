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
exec fn Int2Str(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@),
            Str2Int(res@) == n as nat,
    decreases n,
{
    if n == 0 {
        let mut res = Vec::new();
        res.push('0');
        proof {
            assert(res@.len() == 1);
            assert(res@[0] == '0');
            assert(ValidBitString(res@));
            assert(Str2Int(res@) == 0);
        }
        res
    } else {
        let half = n / 2;
        let mut res = Int2Str(half);
        if n % 2 == 1 {
            res.push('1');
        } else {
            res.push('0');
        }
        proof {
            assert(ValidBitString(res@));
            let old_res = res@.subrange(0, res@.len() - 1);
            assert(old_res == Int2Str(half)@);
            assert(Str2Int(old_res) == half as nat);
            if n % 2 == 1 {
                assert(res@[res@.len() - 1] == '1');
                assert(Str2Int(res@) == 2 * Str2Int(old_res) + 1);
                assert(Str2Int(res@) == 2 * (half as nat) + 1);
                assert(2 * (half as nat) + 1 == n as nat);
            } else {
                assert(res@[res@.len() - 1] == '0');
                assert(Str2Int(res@) == 2 * Str2Int(old_res) + 0);
                assert(Str2Int(res@) == 2 * (half as nat));
                assert(2 * (half as nat) == n as nat);
            }
        }
        res
    }
}

exec fn Str2Int_exec(s: &[char]) -> (res: u64)
    requires ValidBitString(s@),
             s@.len() <= 64,
             Str2Int(s@) < 0x10000000000000000,
    ensures res as nat == Str2Int(s@),
    decreases s@.len(),
{
    if s.len() == 0 {
        0
    } else {
        let prefix = &s[0..s.len() - 1];
        let prefix_val = Str2Int_exec(prefix);
        let last_bit = if s[s.len() - 1] == '1' { 1u64 } else { 0u64 };
        proof {
            assert(s@.subrange(0, s@.len() - 1) == prefix@);
            assert(Str2Int(s@) == 2 * Str2Int(prefix@) + (if s@[s@.len() - 1] == '1' { 1nat } else { 0nat }));
        }
        2 * prefix_val + last_bit
    }
}

exec fn ModMul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
    requires ValidBitString(sx@),
             ValidBitString(sy@),
             ValidBitString(sz@),
             Str2Int(sz@) > 0,
             sx@.len() <= 64,
             sy@.len() <= 64,
             sz@.len() <= 64,
             Str2Int(sx@) < 0x100000000,
             Str2Int(sy@) < 0x100000000,
             Str2Int(sz@) < 0x100000000,
    ensures ValidBitString(res@),
            Str2Int(res@) == (Str2Int(sx@) * Str2Int(sy@)) % Str2Int(sz@),
{
    let x = Str2Int_exec(sx);
    let y = Str2Int_exec(sy);
    let z = Str2Int_exec(sz);
    let product = (x as u128) * (y as u128);
    let result = (product % (z as u128)) as u64;
    proof {
        assert(x as nat == Str2Int(sx@));
        assert(y as nat == Str2Int(sy@));
        assert(z as nat == Str2Int(sz@));
        assert(result as nat == ((x as nat) * (y as nat)) % (z as nat));
    }
    Int2Str(result)
}

exec fn DecrementBitString(s: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s@),
             Str2Int(s@) > 0,
             s@.len() <= 64,
             Str2Int(s@) < 0x10000000000000000,
    ensures ValidBitString(res@),
            Str2Int(res@) == Str2Int(s@) - 1,
{
    let val = Str2Int_exec(s);
    proof {
        assert(val > 0);
        assert(val as nat == Str2Int(s@));
    }
    Int2Str(val - 1)
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
    if sy.len() == 0 || (sy.len() == 1 && sy[0] == '0') {
        // y = 0, so x^0 = 1
        let mut res = Vec::new();
        res.push('1');
        proof {
            assert(res@.len() == 1);
            assert(res@[0] == '1');
            assert(ValidBitString(res@));
            assert(Str2Int(res@) == 1);
            assert(Exp_int(Str2Int(sx@), 0) == 1);
            assert(1nat % Str2Int(sz@) < Str2Int(sz@));
        }
        res
    } else {
        // y > 0, so x^y = x * x^(y-1)
        let sy_minus_1 = DecrementBitString(sy);
        let exp_result = ModExp_DivMod_ModExpPow2_Mul(sx, &sy_minus_1, sz);
        let res = ModMul(sx, &exp_result, sz);
        proof {
            assert(Str2Int(sy_minus_1@) == Str2Int(sy@) - 1);
            assert(Str2Int(exp_result@) == Exp_int(Str2Int(sx@), Str2Int(sy_minus_1@)) % Str2Int(sz@));
            assert(Str2Int(exp_result@) == Exp_int(Str2Int(sx@), (Str2Int(sy@) - 1) as nat) % Str2Int(sz@));
            assert(Str2Int(res@) == (Str2Int(sx@) * Str2Int(exp_result@)) % Str2Int(sz@));
            assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) == Str2Int(sx@) * Exp_int(Str2Int(sx@), (Str2Int(sy@) - 1) as nat));
        }
        res
    }
}
// </vc-code>

fn main() {}
}