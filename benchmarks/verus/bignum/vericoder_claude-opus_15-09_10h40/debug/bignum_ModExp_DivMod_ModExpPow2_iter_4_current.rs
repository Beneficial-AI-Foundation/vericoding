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
/* helper modified by LLM (iteration 4): using ghost variables and exec functions properly */
proof fn lemma_exp_properties(x: nat, y: nat)
    ensures
        y > 0 ==> Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat),
        Exp_int(x, 0) == 1
{
}

proof fn lemma_modexp_base(x: nat, z: nat)
    requires z > 1
    ensures Exp_int(x, 0) % z == 1nat % z
{
}

proof fn lemma_modexp_recursive(x: nat, y: nat, z: nat)
    requires
        y > 0,
        z > 1
    ensures Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
{
}

exec fn str_to_int(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        Str2Int(s@) < 0x10000000000000000
    ensures res as nat == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result as nat == Str2Int(s@.subrange(0, i as int)),
            result < 0x10000000000000000
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    
    result
}

exec fn int_to_str(n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n as nat
{
    let mut result = Vec::<char>::new();
    let mut num = n;
    
    if num == 0 {
        result.push('0');
        return result;
    }
    
    let mut temp = Vec::<char>::new();
    while num > 0
        invariant
            ValidBitString(temp@)
    {
        if num % 2 == 0 {
            temp.push('0');
        } else {
            temp.push('1');
        }
        num = num / 2;
    }
    
    let mut i = temp.len();
    while i > 0
        invariant
            0 <= i <= temp.len(),
            ValidBitString(result@),
            result@.len() == temp.len() - i
    {
        i = i - 1;
        result.push(temp[i]);
    }
    
    result
}

exec fn modexp_exec(base: u64, exp: u64, modulus: u64) -> (res: u64)
    requires
        modulus > 1,
        modulus < 0x10000000000000000
    ensures res as nat == Exp_int(base as nat, exp as nat) % (modulus as nat)
    decreases exp
{
    if exp == 0 {
        proof { lemma_modexp_base(base as nat, modulus as nat); }
        return 1 % modulus;
    } else {
        proof { lemma_modexp_recursive(base as nat, exp as nat, modulus as nat); }
        let base_mod = base % modulus;
        let rec_result = modexp_exec(base, exp - 1, modulus);
        return (base_mod * rec_result) % modulus;
    }
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
    /* code modified by LLM (iteration 4): using exec functions for bitstring conversion */
    let x_val = str_to_int(sx);
    let y_val = str_to_int(sy);
    let z_val = str_to_int(sz);
    
    let result_val = modexp_exec(x_val, y_val, z_val);
    let result = int_to_str(result_val);
    
    result
}
// </vc-code>

fn main() {}
}
