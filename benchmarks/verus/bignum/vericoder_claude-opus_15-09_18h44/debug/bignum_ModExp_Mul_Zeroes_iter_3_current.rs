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
proof fn lemma_exp_properties(x: nat, y: nat, z: nat)
    requires z > 1
    ensures
        y > 0 ==> Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat),
        Exp_int(x, 0) == 1,
{
}

proof fn lemma_mod_properties(a: nat, b: nat, c: nat, m: nat)
    requires m > 1
    ensures
        (a * b) % m == ((a % m) * (b % m)) % m,
        (a + b) % m == ((a % m) + (b % m)) % m,
{
}

/* helper modified by LLM (iteration 3): Changed int_to_bit_string to ghost/spec function */
spec fn int_to_bit_string_spec(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n == 1 {
        seq!['1']
    } else {
        let half = int_to_bit_string_spec(n / 2);
        if n % 2 == 0 {
            half + seq!['0']
        } else {
            half + seq!['1']
        }
    }
}

exec fn int_to_bit_string_exec(n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n,
{
    if n == 0 {
        vec!['0']
    } else if n == 1 {
        vec!['1']
    } else {
        let mut res = int_to_bit_string_exec(n / 2);
        if n % 2 == 0 {
            res.push('0');
        } else {
            res.push('1');
        }
        res
    }
}

exec fn str2int_exec(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        s@.len() <= 64,
    ensures
        res == Str2Int(s@),
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int)),
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    result
}

exec fn mod_mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(sx@),
        ValidBitString(sy@),
        ValidBitString(sz@),
        sx@.len() <= 32,
        sy@.len() <= 32,
        sz@.len() <= 32,
        Str2Int(sz@) > 1,
    ensures
        ValidBitString(res@),
        Str2Int(res@) == (Str2Int(sx@) * Str2Int(sy@)) % Str2Int(sz@),
{
    let x = str2int_exec(sx);
    let y = str2int_exec(sy);
    let z = str2int_exec(sz);
    proof {
        lemma_mod_properties(x as nat, y as nat, 0, z as nat);
    }
    let prod = (x * y) % z;
    int_to_bit_string_exec(prod)
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
    /* code modified by LLM (iteration 3): Use exec functions for actual computation */
    if sy.len() == 1 {
        if sy[0] == '0' {
            proof {
                lemma_exp_properties(Str2Int(sx@), 0, Str2Int(sz@));
            }
            return vec!['1'];
        } else {
            proof {
                lemma_exp_properties(Str2Int(sx@), 1, Str2Int(sz@));
            }
            let x = str2int_exec(sx);
            let z = str2int_exec(sz);
            return int_to_bit_string_exec(x % z);
        }
    }
    
    let sy_prefix = &sy[0..sy.len() - 1];
    let last_bit = sy[sy.len() - 1];
    
    let half_exp = ModExp_Mul_Zeroes(sx, sy_prefix, sz);
    let squared = mod_mul(&half_exp, &half_exp, sz);
    
    if last_bit == '1' {
        let x = str2int_exec(sx);
        let z = str2int_exec(sz);
        let sx_mod = int_to_bit_string_exec(x % z);
        proof {
            lemma_exp_properties(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
            lemma_mod_properties(Exp_int(Str2Int(sx@), Str2Int(sy@) / 2) * Exp_int(Str2Int(sx@), Str2Int(sy@) / 2), Str2Int(sx@), 0, Str2Int(sz@));
        }
        mod_mul(&squared, &sx_mod, sz)
    } else {
        proof {
            lemma_exp_properties(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
        }
        squared
    }
}
// </vc-code>

fn main() {}
}
