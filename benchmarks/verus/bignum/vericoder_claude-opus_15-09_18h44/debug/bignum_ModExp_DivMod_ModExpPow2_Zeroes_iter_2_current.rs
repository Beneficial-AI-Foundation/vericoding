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
proof fn pow_mod_lemma(x: nat, y: nat, z: nat)
    requires
        z > 1
    ensures
        y == 0 ==> Exp_int(x, y) % z == 1nat % z,
        y > 0 ==> Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
    decreases y
{
    if y == 0 {
        assert(Exp_int(x, 0) == 1);
    } else {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    }
}

fn int_to_bitstring(n: nat) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n
    decreases n
{
    if n == 0nat {
        let mut res = Vec::<char>::new();
        res
    } else {
        let mut res = int_to_bitstring((n / 2) as nat);
        if n % 2 == 0nat {
            res.push('0');
        } else {
            res.push('1');
        }
        proof {
            if res@.len() > 0 {
                assert(Str2Int(res@) == 2 * Str2Int(res@.subrange(0, res@.len() as int - 1)) + (if res@.index(res@.len() as int - 1) == '1' { 1nat } else { 0nat }));
            }
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
    /* code modified by LLM (iteration 2): fixed type errors with nat literals */
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    if sy@.len() == 0nat || y_val == 0nat {
        proof {
            pow_mod_lemma(x_val, 0nat, z_val);
            assert(Exp_int(x_val, 0nat) == 1nat);
        }
        let result_val = (1nat % z_val) as nat;
        return int_to_bitstring(result_val);
    } else {
        let mut sy_minus_one = Vec::<char>::new();
        let mut carry = true;
        let mut i: usize = sy.len() - 1;
        
        loop
            invariant
                i <= sy.len(),
                ValidBitString(sy_minus_one@),
                carry ==> (i == sy.len() || (forall |j: int| i <= j && j < sy.len() as int ==> sy_minus_one@[j - i as int] == '0')),
                !carry ==> sy_minus_one@.len() == sy.len() - i,
                !carry ==> Str2Int(sy_minus_one@) + Exp_int(2, i as nat) == y_val
            decreases i
        {
            if i == 0 {
                break;
            }
            
            if carry {
                if sy[i - 1] == '1' {
                    sy_minus_one.push('0');
                    carry = false;
                } else {
                    sy_minus_one.push('1');
                }
            } else {
                sy_minus_one.push(sy[i - 1]);
            }
            i = i - 1;
        }
        
        if carry || sy_minus_one@.len() == 0nat {
            proof {
                assert(y_val == 1nat);
                pow_mod_lemma(x_val, 1nat, z_val);
                assert(Exp_int(x_val, 1nat) == x_val);
            }
            let result_val = (x_val % z_val) as nat;
            return int_to_bitstring(result_val);
        }
        
        let rec_result = ModExp_DivMod_ModExpPow2_Zeroes(sx, &sy_minus_one, sz);
        let rec_val = Str2Int(rec_result@);
        
        proof {
            pow_mod_lemma(x_val, y_val, z_val);
            assert(Exp_int(x_val, y_val) % z_val == ((x_val % z_val) * rec_val) % z_val);
        }
        
        let x_mod = (x_val % z_val) as nat;
        let result_val = ((x_mod * rec_val) % z_val) as nat;
        return int_to_bitstring(result_val);
    }
}
// </vc-code>

fn main() {}
}
