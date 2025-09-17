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
    ensures Str2Int(s.push(bit)) == 2 * Str2Int(s) + if bit == '1' { 1 as nat } else { 0 as nat }
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

proof fn mod_mul_mod(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

exec fn str_to_u64(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), Str2Int(s@) < 0x10000000000000000
    ensures res as nat == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut power: u64 = 1;
    
    for i in 0..s.len()
        invariant
            0 <= i <= s.len(),
            result as nat == Str2Int(s@.subrange(0, i as int)),
            power as nat == Exp_int(2, i as nat),
            result < 0x10000000000000000,
            power <= 0x10000000000000000,
    {
        let old_result = result;
        let old_power = power;
        
        if s[i] == '1' {
            result = result + power;
        }
        
        if i < s.len() - 1 {
            power = power * 2;
        }
        
        proof {
            assert(s@.subrange(0, (i + 1) as int) == s@.subrange(0, i as int).push(s@[i as int]));
            str2int_append_bit(s@.subrange(0, i as int), s@[i as int]);
        }
    }
    
    proof {
        assert(s@.subrange(0, s.len() as int) == s@);
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
        let z_val = str_to_u64(sz);
        let one_mod_z = if z_val <= 1 { 0u64 } else { 1u64 };
        let result = Int2Str(one_mod_z);
        proof {
            assert(Str2Int(sy@) == 0);
            assert(Exp_int(Str2Int(sx@), 0) == 1);
            let z_nat = Str2Int(sz@);
            assert(z_nat > 1);
            assert(z_val as nat == z_nat);
            assert(1 % z_nat == 1);
            assert(one_mod_z as nat == 1);
            assert(Str2Int(result@) == 1);
            assert(Str2Int(result@) == 1 % z_nat);
        }
        return result;
    }
    
    // Compute x^2 for the recursive call
    let x_val = str_to_u64(sx);
    let z_val = str_to_u64(sz);
    let x_squared = (x_val * x_val) % z_val;
    let x_squared_str = Int2Str(x_squared);
    
    // Recursive case based on last bit
    let last_bit = sy[sy.len() - 1];
    let sy_half = &sy[0..sy.len() - 1];
    
    proof {
        assert(sy_half@ == sy@.subrange(0, sy@.len() as int - 1));
        assert(ValidBitString(sy_half@)) by {
            assert forall |i: int| 0 <= i && i < sy_half@.len() as int implies 
                sy_half@[i] == '0' || sy_half@[i] == '1' by {
                assert(sy_half@[i] == sy@[i]);
            }
        }
        assert(Str2Int(sy@) == 2 * Str2Int(sy_half@) + if last_bit == '1' { 1 as nat } else { 0 as nat });
    }
    
    if sy_half.len() == 0 {
        // Base case: y = 1 (since last_bit must be '1' if we're here with non-zero y)
        if last_bit == '1' {
            let result_val = x_val % z_val;
            let result = Int2Str(result_val);
            proof {
                assert(Str2Int(sy@) == 1);
                assert(Exp_int(Str2Int(sx@), 1) == Str2Int(sx@));
                assert(Str2Int(result@) == Str2Int(sx@) % Str2Int(sz@));
            }
            return result;
        } else {
            // y = 0, already handled above
            return Int2Str(1);
        }
    }
    
    // Recursive call with x^2 and y/2
    let rec_result = ModExp_DivMod_ModExpPow2(&x_squared_str, sy_half, sz);
    let rec_val = str_to_u64(&rec_result);
    
    let result_val = if last_bit == '1' {
        // y is odd: result = x * (x^2)^(y/2) mod z
        ((x_val % z_val) * rec_val) % z_val
    } else {
        // y is even: result = (x^2)^(y/2) mod z
        rec_val
    };
    
    let result = Int2Str(result_val);
    
    proof {
        let x_nat = Str2Int(sx@);
        let y_nat = Str2Int(sy@);
        let z_nat = Str2Int(sz@);
        let y_half = Str2Int(sy_half@);
        
        assert(x_squared as nat == (x_nat * x_nat) % z_nat);
        assert(Str2Int(x_squared_str@) == x_squared as nat);
        assert(Str2Int(rec_result@) == Exp_int((x_nat * x_nat) % z_nat, y_half) % z_nat);
        
        if last_bit == '1' {
            assert(y_nat == 2 * y_half + 1);
            exp_int_odd(x_nat, y_nat);
            assert(Exp_int(x_nat, y_nat) == x_nat * Exp_int(x_nat * x_nat, y_half));
            mod_mul_mod(x_nat, Exp_int(x_nat * x_nat, y_half), z_nat);
            mod_mul_mod(x_nat * x_nat, 1, z_nat);
            assert(Exp_int(x_nat * x_nat, y_half) % z_nat == Exp_int((x_nat * x_nat) % z_nat, y_half) % z_nat);
        } else {
            assert(y_nat == 2 * y_half);
            exp_int_even(x_nat, y_nat);
            assert(Exp_int(x_nat, y_nat) == Exp_int(x_nat * x_nat, y_half));
            assert(Exp_int(x_nat * x_nat, y_half) % z_nat == Exp_int((x_nat * x_nat) % z_nat, y_half) % z_nat);
        }
        
        assert(Str2Int(result@) == Exp_int(x_nat, y_nat) % z_nat);
    }
    
    result
}
// </vc-code>

fn main() {}
}