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
proof fn lemma_exp_split(x: nat, y: nat, z: nat)
    requires z > 1
    ensures Exp_int(x, y) % z == if y == 0 { 1 % z } else { ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z }
{
    if y == 0 {
        assert(Exp_int(x, y) == 1);
    } else {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    }
}

proof fn lemma_mod_mul(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

exec fn str_to_int_exec(s: &[char]) -> (res: u64)
    requires ValidBitString(s@),
        s@.len() <= 64,
    ensures res as nat == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result as nat == Str2Int(s@.subrange(0, i as int)),
            ValidBitString(s@),
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    assert(s@.subrange(0, s@.len() as int) =~= s@);
    result
}

exec fn int_to_str_exec(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@),
        Str2Int(res@) == n as nat
{
    let mut result = Vec::<char>::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    while n > 0
        invariant
            ValidBitString(result@),
            n as nat * Exp_int(2, result@.len() as nat) + Str2Int(result@) == old(n) as nat,
    {
        if n % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        n = n / 2;
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 1 && sy[0] == '0' {
        let mut res = Vec::<char>::new();
        res.push('1');
        return res;
    }
    
    let x_val = str_to_int_exec(sx);
    let z_val = str_to_int_exec(sz);
    
    if sy.len() == 1 && sy[0] == '1' {
        let res_val = x_val % z_val;
        return int_to_str_exec(res_val);
    }
    
    let mut sy_half = Vec::<char>::new();
    for i in 0..(sy.len() - 1) {
        sy_half.push(sy[i]);
    }
    
    let half_res = ModExp_Mul_Zeroes(&sy_half, &sy_half, sz);
    let half_val = str_to_int_exec(&half_res);
    
    let mut result_val = (half_val * half_val) % z_val;
    
    if sy[sy.len() - 1] == '1' {
        result_val = (result_val * (x_val % z_val)) % z_val;
    }
    
    proof {
        lemma_exp_split(x_val as nat, Str2Int(sy@), z_val as nat);
        lemma_mod_mul(half_val as nat, half_val as nat, z_val as nat);
        if sy[sy.len() - 1] == '1' {
            lemma_mod_mul(result_val as nat, x_val as nat, z_val as nat);
        }
    }
    
    int_to_str_exec(result_val)
}
// </vc-code>

fn main() {}
}
