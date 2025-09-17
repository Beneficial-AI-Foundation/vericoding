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
    } else {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    }
}

/* helper modified by LLM (iteration 4): Added decreases clause to while loop */
spec fn int_to_binary_spec(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n == 1 {
        seq!['1']
    } else {
        let rest = int_to_binary_spec(n / 2);
        if n % 2 == 0 {
            rest.push('0')
        } else {
            rest.push('1')
        }
    }
}

fn int_to_binary(n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n
{
    let mut result = Vec::<char>::new();
    let mut num = n;
    
    if num == 0 {
        result.push('0');
        return result;
    }
    
    while num > 0
        invariant
            ValidBitString(result@),
            num >= 0,
        decreases num
    {
        if num % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2;
    }
    
    let mut i: usize = 0;
    let mut j = result.len() - 1;
    while i < j
        invariant
            ValidBitString(result@),
            0 <= i <= j < result.len(),
        decreases j - i
    {
        let temp = result[i];
        result.set(i, result[j]);
        result.set(j, temp);
        i = i + 1;
        j = j - 1;
    }
    
    result
}

fn binary_to_int(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@)
    ensures
        res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int)),
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
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): No changes needed in code section */
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
    
    let y_minus_1_binary = int_to_binary(y - 1);
    let rec_result = ModExp_DivMod_ModExpPow2_Mul(sx, &y_minus_1_binary, sz);
    let rec_val = binary_to_int(&rec_result);
    
    let x_mod_z = x % z;
    let result_val = (x_mod_z * rec_val) % z;
    
    proof {
        pow_mod_lemma(x as nat, y as nat, z as nat);
        assert(rec_val == Exp_int(x as nat, (y - 1) as nat) % (z as nat));
        assert(Exp_int(x as nat, y as nat) % (z as nat) == ((x as nat % z as nat) * (Exp_int(x as nat, (y - 1) as nat) % (z as nat))) % (z as nat));
        assert(result_val == Exp_int(x as nat, y as nat) % (z as nat));
    }
    
    int_to_binary(result_val)
}
// </vc-code>

fn main() {}
}
