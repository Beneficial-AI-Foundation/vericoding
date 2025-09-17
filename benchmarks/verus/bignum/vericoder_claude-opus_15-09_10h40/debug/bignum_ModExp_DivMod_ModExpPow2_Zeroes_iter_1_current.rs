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
proof fn lemma_exp_int_split(x: nat, y: nat)
    ensures
        y > 0 ==> Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
    if y > 0 {
        reveal(Exp_int);
    }
}

proof fn lemma_exp_int_mod(x: nat, y: nat, z: nat)
    requires
        z > 1,
        y > 0
    ensures
        Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
{
    lemma_exp_int_split(x, y);
    assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    assert(Exp_int(x, y) % z == (x * Exp_int(x, (y - 1) as nat)) % z);
    assert((x * Exp_int(x, (y - 1) as nat)) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z) by {
        let a = x;
        let b = Exp_int(x, (y - 1) as nat);
        assert((a * b) % z == ((a % z) * (b % z)) % z);
    }
}

exec fn int_to_bit_string(n: nat) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n
    decreases n
{
    if n == 0 {
        Vec::<char>::new()
    } else {
        let mut res = int_to_bit_string((n / 2) as nat);
        if n % 2 == 1 {
            res.push('1');
        } else {
            res.push('0');
        }
        res
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);
    
    if sy.len() == 0 {
        assert(y == 0);
        assert(Exp_int(x, y) == 1) by { reveal(Exp_int); }
        let result = int_to_bit_string((1 % z) as nat);
        return result;
    } else if sy[sy.len() - 1] == '0' {
        let sy_half = &sy[0..sy.len() - 1];
        assert(ValidBitString(sy_half@));
        assert(Str2Int(sy@) == 2 * Str2Int(sy_half@)) by {
            reveal(Str2Int);
        }
        
        let temp = ModExp_DivMod_ModExpPow2_Zeroes(sx, sy_half, sz);
        assert(Str2Int(temp@) == Exp_int(x, Str2Int(sy_half@)) % z);
        
        let temp_val = Str2Int(temp@);
        let res_val = ((temp_val * temp_val) % z) as nat;
        
        proof {
            assert(y == 2 * Str2Int(sy_half@));
            assert(Exp_int(x, y) == Exp_int(Exp_int(x, Str2Int(sy_half@)), 2)) by {
                reveal(Exp_int);
                assert(Exp_int(x, y) == Exp_int(x, 2 * Str2Int(sy_half@)));
            }
            assert(Exp_int(Exp_int(x, Str2Int(sy_half@)), 2) == Exp_int(x, Str2Int(sy_half@)) * Exp_int(x, Str2Int(sy_half@))) by {
                reveal(Exp_int);
            }
            assert(Exp_int(x, y) % z == ((Exp_int(x, Str2Int(sy_half@)) % z) * (Exp_int(x, Str2Int(sy_half@)) % z)) % z);
        }
        
        return int_to_bit_string(res_val);
    } else {
        assert(sy[sy.len() - 1] == '1');
        let sy_minus_one = if sy.len() == 1 {
            Vec::<char>::new()
        } else {
            let mut v = Vec::<char>::new();
            for i in 0..(sy.len() - 1) {
                v.push(sy[i]);
            }
            v[v.len() - 1] = '0';
            v
        };
        
        assert(ValidBitString(sy_minus_one@));
        assert(Str2Int(sy@) == Str2Int(sy_minus_one@) + 1) by {
            reveal(Str2Int);
        }
        
        let temp = ModExp_DivMod_ModExpPow2_Zeroes(sx, &sy_minus_one, sz);
        let res_val = ((x % z) * Str2Int(temp@)) % z;
        
        proof {
            lemma_exp_int_mod(x, y, z);
        }
        
        return int_to_bit_string(res_val as nat);
    }
}
// </vc-code>

fn main() {}
}
