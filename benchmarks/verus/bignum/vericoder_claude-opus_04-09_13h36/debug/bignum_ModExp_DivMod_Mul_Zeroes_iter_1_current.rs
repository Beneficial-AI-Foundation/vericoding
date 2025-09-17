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
// Helper lemmas for modular arithmetic
proof fn lemma_mod_mul(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

proof fn lemma_exp_unfold(x: nat, y: nat)
    requires y > 0
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
}

proof fn lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

// Convert a natural number to a binary string
exec fn Int2Str(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == n
{
    let mut result = Vec::<char>::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    
    while n > 0
        invariant ValidBitString(result@)
        invariant n + Str2Int(result@) * Exp_int(2, result@.len() as nat) == old(n)
    {
        if n % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        n = n / 2;
    }
    
    // Reverse the result
    let mut i: usize = 0;
    let mut j = result.len() - 1;
    while i < j
        invariant ValidBitString(result@)
        invariant Str2Int(result@) == old(n)
        invariant 0 <= i <= j < result.len()
    {
        let temp = result[i];
        result.set(i, result[j]);
        result.set(j, temp);
        i = i + 1;
        j = j - 1;
    }
    
    result
}

// Convert binary string to u64
exec fn Str2Int_exec(s: &[char]) -> (res: u64)
    requires ValidBitString(s@)
    requires s@.len() <= 64
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant 0 <= i <= s.len()
        invariant ValidBitString(s@)
        invariant result == Str2Int(s@.subrange(0, i as int))
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
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    // Base case: if y is "0", return "1"
    if sy.len() == 1 && sy[0] == '0' {
        proof {
            lemma_exp_zero(Str2Int(sx@));
            assert(Str2Int(sy@) == 0);
            assert(Exp_int(Str2Int(sx@), 0) == 1);
        }
        let mut res = Vec::<char>::new();
        res.push('1');
        return res;
    }
    
    // Convert inputs to integers for computation
    let x_val = Str2Int_exec(sx);
    let y_val = Str2Int_exec(sy);
    let z_val = Str2Int_exec(sz);
    
    // Compute x^y mod z using repeated squaring
    let mut result: u64 = 1;
    let mut base = x_val % z_val;
    let mut exp = y_val;
    
    while exp > 0
        invariant z_val > 1
        invariant result < z_val
        invariant base < z_val
        invariant result * Exp_int(base as nat, exp as nat) % z_val == Exp_int(x_val as nat, y_val as nat) % z_val
    {
        if exp % 2 == 1 {
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        exp = exp / 2;
        
        proof {
            lemma_mod_mul(result as nat, base as nat, z_val as nat);
        }
    }
    
    // Convert result back to binary string
    Int2Str(result)
}
// </vc-code>

fn main() {}
}