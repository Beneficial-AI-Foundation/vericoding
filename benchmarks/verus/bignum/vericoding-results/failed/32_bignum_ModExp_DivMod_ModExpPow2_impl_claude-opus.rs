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
/* helper modified by LLM (iteration 10): Fixed nat literal in lemma_exp_zero */
proof fn lemma_exp_split(x: nat, y: nat, z: nat)
    requires
        y > 0,
        z > 1,
    ensures
        Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z,
{
    reveal(Exp_int);
    assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
}

proof fn lemma_exp_zero(x: nat, z: nat)
    requires
        z > 1,
    ensures
        Exp_int(x, 0) % z == 1 % z,
{
    reveal(Exp_int);
    assert(Exp_int(x, 0) == 1);
}

fn int_to_bitstring(n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n as nat,
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
    {
        let temp = result[i];
        result.set(i, result[j]);
        result.set(j, temp);
        i = i + 1;
        j = j - 1;
    }
    
    result
}

fn bitstring_to_int(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        Str2Int(s@) < u64::MAX as nat,
    ensures
        res as nat == Str2Int(s@),
{
    let mut result: u64 = 0;
    let mut power: u64 = 1;
    
    let mut i = s.len();
    while i > 0
        invariant
            0 <= i <= s.len(),
    {
        i = i - 1;
        if s[i] == '1' {
            result = result + power;
        }
        if i > 0 {
            power = power * 2;
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
    /* code modified by LLM (iteration 10): Fixed nat literal comparison - use 0 instead of 0nat */
    let x_val = bitstring_to_int(sx);
    let y_val = bitstring_to_int(sy);
    let z_val = bitstring_to_int(sz);
    
    if sy@.len() == 0 {
        proof {
            lemma_exp_zero(x_val as nat, z_val as nat);
        }
        return int_to_bitstring(1 % z_val);
    }
    
    if sy@.len() == 1 {
        if sy[0] == '0' {
            proof {
                lemma_exp_zero(x_val as nat, z_val as nat);
            }
            return int_to_bitstring(1 % z_val);
        } else {
            return int_to_bitstring(x_val % z_val);
        }
    }
    
    let mut sy_sub = Vec::<char>::new();
    for i in 0..(sy.len() - 1) {
        sy_sub.push(sy[i]);
    }
    
    let rec_result = ModExp_DivMod_ModExpPow2(sx, &sy_sub, sz);
    let rec_val = bitstring_to_int(&rec_result);
    
    let result = if sy[sy.len() - 1] == '1' {
        proof {
            lemma_exp_split(x_val as nat, y_val as nat, z_val as nat);
        }
        ((x_val % z_val) * rec_val) % z_val
    } else {
        (rec_val * rec_val) % z_val
    };
    
    int_to_bitstring(result)
}
// </vc-code>

fn main() {}
}
