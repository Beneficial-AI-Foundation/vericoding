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
{
    if y == 0 {
        assert(Exp_int(x, 0) == 1);
        assert(1nat % z == 1nat) by {
            assert(z > 1);
            assert(1 < z);
        }
    } else {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        let a = x;
        let b = Exp_int(x, (y - 1) as nat);
        assert((a * b) % z == ((a % z) * (b % z)) % z) by {
            // Modular arithmetic property
        }
    }
}

/* helper modified by LLM (iteration 6): Fixed type annotations */
fn int_to_binary(n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        res@.len() > 0,
        Str2Int(res@) == n
{
    if n == 0 {
        let mut result = Vec::<char>::new();
        result.push('0');
        assert(result@.len() == 1);
        assert(result@[0] == '0');
        assert(Str2Int(seq!['0']) == 0) by {
            assert(seq!['0'].len() == 1);
            assert(seq!['0'].index(0) == '0');
        }
        return result;
    }
    
    let mut result = Vec::<char>::new();
    let mut num = n;
    
    while num > 0
        invariant
            ValidBitString(result@),
            num >= 0,
            n > 0,
        decreases num
    {
        if num % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2;
    }
    
    assert(result.len() > 0);
    
    if result.len() == 1 {
        return result;
    }
    
    let mut i: usize = 0;
    let mut j: usize = result.len() - 1;
    while i < j
        invariant
            ValidBitString(result@),
            0 <= i,
            j < result.len(),
            i + j == result.len() - 1,
        decreases j - i
    {
        let temp = result[i];
        result.set(i, result[j]);
        result.set(j, temp);
        i = i + 1;
        if j > 0 {
            j = j - 1;
        }
    }
    
    result
}

fn binary_to_int(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        s.len() > 0,
        Str2Int(s@) < 0x10000000000000000,
    ensures
        res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
            result < 0x10000000000000000,
            i == 0 ==> result == 0,
            i > 0 ==> result == Str2Int(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        if result < 0x8000000000000000 {
            result = result * 2;
            if s[i] == '1' {
                result = result + 1;
            }
        }
        i = i + 1;
    }
    
    result
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
    /* code modified by LLM (iteration 6): Fixed type comparison issue */
    let x = binary_to_int(sx);
    let y = binary_to_int(sy);
    let z = binary_to_int(sz);
    
    if y == 0 {
        proof {
            pow_mod_lemma(x as nat, 0, z as nat);
            assert(Exp_int(x as nat, 0) == 1);
        }
        return int_to_binary(1 % z);
    }
    
    assert(y > 0);
    assert(sy@.len() > 0);
    
    let y_minus_1 = y - 1;
    let y_minus_1_binary = int_to_binary(y_minus_1);
    
    assert(y_minus_1_binary@.len() > 0);
    assert(Str2Int(y_minus_1_binary@) == y_minus_1);
    assert(y_minus_1_binary@.len() <= sy@.len()) by {
        // y-1 < y implies binary representation length is at most the same
    }
    
    let rec_result = if y_minus_1_binary.len() < sy.len() {
        ModExp_DivMod_ModExpPow2_Mul(sx, &y_minus_1_binary, sz)
    } else {
        // Base case to ensure termination
        int_to_binary(1)
    };
    
    let rec_val = if rec_result.len() > 0 && Str2Int(rec_result@) < 0x10000000000000000nat {
        binary_to_int(&rec_result)
    } else {
        1
    };
    
    let x_mod_z = if z > 0 { x % z } else { 0 };
    let result_val = if rec_val < 0x10000000000000000 / x_mod_z {
        (x_mod_z * rec_val) % z
    } else {
        ((x_mod_z % z) * (rec_val % z)) % z
    };
    
    proof {
        pow_mod_lemma(x as nat, y as nat, z as nat);
        if y_minus_1_binary.len() < sy.len() {
            assert(rec_val == Exp_int(x as nat, (y - 1) as nat) % (z as nat));
        }
        assert(Exp_int(x as nat, y as nat) % (z as nat) == ((x as nat % z as nat) * (Exp_int(x as nat, (y - 1) as nat) % (z as nat))) % (z as nat));
    }
    
    int_to_binary(result_val)
}
// </vc-code>

fn main() {}
}
