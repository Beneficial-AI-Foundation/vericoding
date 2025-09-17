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
proof fn str2int_append_bit(s: Seq<char>, bit: char)
    requires ValidBitString(s), bit == '0' || bit == '1'
    ensures Str2Int(s.push(bit)) == 2 * Str2Int(s) + if bit == '1' { 1nat } else { 0nat }
    decreases s.len()
{
    let s_new = s.push(bit);
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) == s);
    assert(s_new.index(s_new.len() as int - 1) == bit);
}

proof fn exp_int_even(x: nat, y: nat)
    requires y > 0, y % 2 == 0
    ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
    decreases y
{
    if y == 2 {
        assert(Exp_int(x, 2) == x * x * 1);
        assert(Exp_int(x * x, 1) == x * x * 1);
    } else {
        assert(y >= 2);
        let y_half = y / 2;
        assert(y == 2 * y_half);
        exp_int_even(x, (y - 2) as nat);
        assert(Exp_int(x, y) == x * x * Exp_int(x, (y - 2) as nat));
        assert(Exp_int(x, (y - 2) as nat) == Exp_int(x * x, ((y - 2) / 2) as nat));
        assert((y - 2) / 2 == y_half - 1);
    }
}

proof fn exp_int_odd(x: nat, y: nat)
    requires y > 0, y % 2 == 1
    ensures Exp_int(x, y) == x * Exp_int(x * x, y / 2)
    decreases y
{
    if y == 1 {
        assert(Exp_int(x, 1) == x * 1);
        assert(Exp_int(x * x, 0) == 1);
    } else {
        assert(y >= 3);
        let y_half = y / 2;
        assert(y == 2 * y_half + 1);
        exp_int_odd(x, (y - 2) as nat);
        assert(Exp_int(x, y) == x * x * Exp_int(x, (y - 2) as nat));
        assert(y - 2 == 2 * y_half - 1);
        assert(Exp_int(x, (y - 2) as nat) == x * Exp_int(x * x, ((y - 2) / 2) as nat));
        assert((y - 2) / 2 == y_half - 1);
        assert(Exp_int(x, y) == x * x * x * Exp_int(x * x, (y_half - 1) as nat));
        assert(Exp_int(x * x, y_half) == x * x * Exp_int(x * x, (y_half - 1) as nat));
    }
}

exec fn Int2Str(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n as nat
{
    let mut result = Vec::<char>::new();
    let mut num = n;
    
    if num == 0 {
        result.push('0');
        proof {
            assert(result@.len() == 1);
            assert(result@[0] == '0');
            assert(ValidBitString(result@));
            assert(Str2Int(result@) == 0);
        }
    } else {
        while num > 0
            invariant
                ValidBitString(result@),
                Str2Int(result@) + (num as nat) * Exp_int(2, result@.len() as nat) == n as nat,
        {
            let old_result = result;
            let old_num = num;
            
            if num % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            num = num / 2;
            
            proof {
                str2int_append_bit(old_result@, if old_num % 2 == 1 { '1' } else { '0' });
                assert(Str2Int(result@) == 2 * Str2Int(old_result@) + (old_num % 2) as nat);
                assert(Exp_int(2, result@.len() as nat) == 2 * Exp_int(2, old_result@.len() as nat));
            }
        }
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        panic!(); // This case should not happen due to precondition sy@.len() > 0
    }
    
    if sy.len() == 1 && sy[0] == '0' {
        // y = 0, so x^0 = 1
        let z_nat = Str2Int(sz@);
        let one_mod_z = (1 % z_nat) as u64;
        let result = Int2Str(one_mod_z);
        proof {
            assert(Str2Int(sy@) == 0);
            assert(Exp_int(Str2Int(sx@), 0) == 1);
            assert(Str2Int(result@) == 1 % z_nat);
        }
        return result;
    }
    
    // Recursive case: y > 0
    // We compute using the recurrence relation from the spec
    let sy_prefix = &sy[0..sy.len() - 1];
    
    proof {
        assert(sy_prefix@.len() == sy@.len() - 1);
        assert(sy_prefix@ == sy@.subrange(0, sy@.len() as int - 1));
        assert(ValidBitString(sy_prefix@)) by {
            assert forall |i: int| 0 <= i && i < sy_prefix@.len() as int implies 
                sy_prefix@[i] == '0' || sy_prefix@[i] == '1' by {
                assert(sy_prefix@[i] == sy@[i]);
            }
        }
    }
    
    // Recursive call with y-1
    let temp_result = ModExp_DivMod_ModExpPow2(sx, sy_prefix, sz);
    
    // Multiply by x and take modulo z
    let x_nat = Str2Int(sx@);
    let z_nat = Str2Int(sz@);
    let temp_nat = Str2Int(temp_result@);
    
    let x_val = x_nat as u64;
    let z_val = z_nat as u64;
    let temp_val = temp_nat as u64;
    
    let last_bit = sy[sy.len() - 1];
    let y_val = if last_bit == '1' {
        2nat * Str2Int(sy_prefix@) + 1nat
    } else {
        2nat * Str2Int(sy_prefix@)
    };
    
    proof {
        assert(Str2Int(sy@) == y_val);
        if last_bit == '1' {
            assert(Str2Int(sy@) > 0);
        } else {
            assert(sy_prefix@.len() > 0) by {
                if sy_prefix@.len() == 0 {
                    assert(sy@.len() == 1);
                    assert(sy@[0] == '0');
                    assert(Str2Int(sy@) == 0);
                    assert(false); // Contradiction with y > 0 from recursive case
                }
            }
            assert(Str2Int(sy@) > 0);
        }
    }
    
    let result_val = (x_val * temp_val) % z_val;
    let result = Int2Str(result_val);
    
    proof {
        assert(temp_nat == Exp_int(Str2Int(sx@), Str2Int(sy_prefix@)) % z_nat);
        assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) == 
               Str2Int(sx@) * Exp_int(Str2Int(sx@), (Str2Int(sy@) - 1) as nat));
        assert((Str2Int(sy@) - 1) as nat == Str2Int(sy_prefix@));
        assert((result_val as nat) == ((x_nat * (Exp_int(x_nat, Str2Int(sy_prefix@)) % z_nat)) % z_nat));
        assert((result_val as nat) == Exp_int(x_nat, Str2Int(sy@)) % z_nat);
        assert(Str2Int(result@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    result
}
// </vc-code>

fn main() {}
}