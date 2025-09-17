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
spec fn ModExpSpec(x: nat, y: nat, z: nat) -> nat
    recommends z > 0
{
    if y == 0 { 
        1 % z 
    } else {
        (x * ModExpSpec(x, (y - 1) as nat, z)) % z
    }
}

proof fn mod_exp_equiv(x: nat, y: nat, z: nat)
    requires z > 0
    ensures ModExpSpec(x, y, z) == Exp_int(x, y) % z
    decreases y
{
    if y == 0 {
        assert(ModExpSpec(x, 0, z) == 1 % z);
        assert(Exp_int(x, 0) == 1);
    } else {
        mod_exp_equiv(x, (y - 1) as nat, z);
        assert(ModExpSpec(x, y, z) == (x * ModExpSpec(x, (y - 1) as nat, z)) % z);
        assert(ModExpSpec(x, (y - 1) as nat, z) == Exp_int(x, (y - 1) as nat) % z);
        assert((x * (Exp_int(x, (y - 1) as nat) % z)) % z == (x * Exp_int(x, (y - 1) as nat)) % z);
    }
}

exec fn Int2Str(n: nat) -> (res: Vec<char>) 
    ensures ValidBitString(res@),
    ensures Str2Int(res@) == n,
    decreases n,
{
    if n == 0 {
        let mut res = Vec::<char>::new();
        res.push('0');
        proof {
            assert(res@.len() == 1);
            assert(res@[0] == '0');
            assert(Str2Int(res@) == 0);
        }
        res
    } else {
        let mut res = Int2Str(n / 2);
        if n % 2 == 0 {
            res.push('0');
        } else {
            res.push('1');
        }
        proof {
            assert(ValidBitString(res@.subrange(0, res@.len() as int - 1)));
            assert(res@.subrange(0, res@.len() as int - 1) == Int2Str(n / 2)@);
            if n % 2 == 0 {
                assert(res@[res@.len() as int - 1] == '0');
                assert(Str2Int(res@) == 2 * Str2Int(res@.subrange(0, res@.len() as int - 1)) + 0);
            } else {
                assert(res@[res@.len() as int - 1] == '1');
                assert(Str2Int(res@) == 2 * Str2Int(res@.subrange(0, res@.len() as int - 1)) + 1);
            }
            assert(Str2Int(res@.subrange(0, res@.len() as int - 1)) == n / 2);
            assert(Str2Int(res@) == 2 * (n / 2) + n % 2);
            assert(2 * (n / 2) + n % 2 == n);
        }
        res
    }
}

exec fn ModMul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
    requires ValidBitString(sx@),
    requires ValidBitString(sy@),
    requires ValidBitString(sz@),
    requires Str2Int(sz@) > 0,
    ensures ValidBitString(res@),
    ensures Str2Int(res@) == (Str2Int(sx@) * Str2Int(sy@)) % Str2Int(sz@),
{
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);
    let prod = (x * y) % z;
    Int2Str(prod)
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        // y = 0, so x^0 = 1
        let mut res = Vec::<char>::new();
        res.push('1');
        proof {
            assert(res@.len() == 1);
            assert(res@[0] == '1');
            assert(ValidBitString(res@));
            assert(Str2Int(res@) == 1);
            assert(Exp_int(Str2Int(sx@), 0) == 1);
            assert(Str2Int(res@) == Exp_int(Str2Int(sx@), 0) % Str2Int(sz@));
        }
        return res;
    }
    
    // Recursive case: compute x^(y-1) mod z first
    let mut sy_minus_1 = Vec::<char>::new();
    let y_val = Str2Int(sy@);
    
    if y_val == 1 {
        // Base case: x^1 mod z = x mod z
        let x_val = Str2Int(sx@);
        let z_val = Str2Int(sz@);
        let result = x_val % z_val;
        let res = Int2Str(result);
        proof {
            assert(Exp_int(x_val, 1) == x_val);
            assert(Str2Int(res@) == x_val % z_val);
            assert(Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
        }
        return res;
    } else {
        // y > 1: compute y - 1 in binary
        sy_minus_1 = Int2Str((y_val - 1) as nat);
        proof {
            assert(Str2Int(sy_minus_1@) == (y_val - 1) as nat);
        }
        
        // Recursive call: compute x^(y-1) mod z
        let rec_result = ModExp_ModExpPow2_Zeroes(sx, &sy_minus_1, sz);
        
        // Multiply by x and take mod z
        let res = ModMul(sx, &rec_result, sz);
        
        proof {
            assert(Str2Int(rec_result@) == Exp_int(Str2Int(sx@), (y_val - 1) as nat) % Str2Int(sz@));
            assert(Str2Int(res@) == (Str2Int(sx@) * Str2Int(rec_result@)) % Str2Int(sz@));
            assert(Str2Int(res@) == (Str2Int(sx@) * (Exp_int(Str2Int(sx@), (y_val - 1) as nat) % Str2Int(sz@))) % Str2Int(sz@));
            mod_exp_equiv(Str2Int(sx@), y_val, Str2Int(sz@));
            assert(ModExpSpec(Str2Int(sx@), y_val, Str2Int(sz@)) == Exp_int(Str2Int(sx@), y_val) % Str2Int(sz@));
            assert((Str2Int(sx@) * (Exp_int(Str2Int(sx@), (y_val - 1) as nat) % Str2Int(sz@))) % Str2Int(sz@) == 
                   (Str2Int(sx@) * Exp_int(Str2Int(sx@), (y_val - 1) as nat)) % Str2Int(sz@));
            assert(Exp_int(Str2Int(sx@), y_val) == Str2Int(sx@) * Exp_int(Str2Int(sx@), (y_val - 1) as nat));
            assert(Str2Int(res@) == Exp_int(Str2Int(sx@), y_val) % Str2Int(sz@));
            assert(Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
        }
        return res;
    }
}
// </vc-code>

fn main() {}
}