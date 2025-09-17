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
/* helper modified by LLM (iteration 2): fixed type annotation for literal 1 in spec functions */
spec fn power_mod(base: nat, exp: nat, modulus: nat) -> nat
    recommends modulus > 1
    decreases exp
{
    if exp == 0 {
        1nat % modulus
    } else {
        ((base % modulus) * power_mod(base, (exp - 1) as nat, modulus)) % modulus
    }
}

proof fn power_mod_correct(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures power_mod(base, exp, modulus) == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
        assert(Exp_int(base, 0) == 1);
        assert(power_mod(base, 0, modulus) == 1nat % modulus);
    } else {
        power_mod_correct(base, (exp - 1) as nat, modulus);
        assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
        assert(power_mod(base, exp, modulus) == ((base % modulus) * power_mod(base, (exp - 1) as nat, modulus)) % modulus);
        assert(((base % modulus) * (Exp_int(base, (exp - 1) as nat) % modulus)) % modulus == (base * Exp_int(base, (exp - 1) as nat)) % modulus);
    }
}

exec fn int_to_bitstring(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    let mut result = Vec::<char>::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    let mut current = n;
    let original = n;
    while current > 0
        invariant
            ValidBitString(result@),
            current as nat * Exp_int(2, result@.len() as nat) + Str2Int(result@) == original as nat,
        decreases current
    {
        if current % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        current = current / 2;
    }
    result
}

exec fn bitstring_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), Str2Int(s@) < 0x10000000000000000
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int)),
            Str2Int(s@.subrange(0, i as int)) < 0x10000000000000000,
        decreases s.len() - i
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    result
}

exec fn mod_exp_exec(base: u64, exp: u64, modulus: u64) -> (res: u64)
    requires modulus > 1, modulus < 0x100000000
    ensures res == power_mod(base as nat, exp as nat, modulus as nat)
    decreases exp
{
    if exp == 0 {
        return 1 % modulus;
    }
    let base_mod = base % modulus;
    let rec_result = mod_exp_exec(base, exp - 1, modulus);
    ((base_mod as u128 * rec_result as u128) % modulus as u128) as u64
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): main implementation */
{
    let x_val = bitstring_to_int(sx);
    let y_val = bitstring_to_int(sy);
    let z_val = bitstring_to_int(sz);
    
    let result_val = mod_exp_exec(x_val, y_val, z_val);
    
    proof {
        power_mod_correct(x_val as nat, y_val as nat, z_val as nat);
        assert(result_val == power_mod(x_val as nat, y_val as nat, z_val as nat));
        assert(power_mod(x_val as nat, y_val as nat, z_val as nat) == Exp_int(x_val as nat, y_val as nat) % (z_val as nat));
        assert(x_val == Str2Int(sx@));
        assert(y_val == Str2Int(sy@));
        assert(z_val == Str2Int(sz@));
    }
    
    let result = int_to_bitstring(result_val);
    assert(Str2Int(result@) == result_val);
    assert(result_val == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    result
}
// </vc-code>

fn main() {}
}
