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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

spec fn AllZero(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0'
}

// <vc-helpers>
proof fn lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

proof fn lemma_exp_succ(x: nat, y: nat)
    ensures y > 0 ==> Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
}

proof fn lemma_mod_mul(a: nat, b: nat, c: nat, m: nat)
    requires m > 1
    ensures ((a % m) * (b % m) * (c % m)) % m == (a * b * c) % m
{
}

proof fn lemma_exp_mod(base: nat, exp: nat, m: nat)
    requires m > 1,
        exp > 0
    ensures Exp_int(base, exp) % m == (base % m * Exp_int(base, (exp - 1) as nat) % m) % m
{
}

spec fn char_to_nat(c: char) -> nat
{
    if c == '1' { 1 } else { 0 }
}

/* helper modified by LLM (iteration 4): fixed slice indexing to use usize end index */
exec fn str_to_int(s: &[char]) -> (res: usize)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
    decreases s@.len()
{
    if s.len() == 0 {
        0
    } else {
        let last_idx: usize = s.len() - 1;
        let sub = if last_idx == 0 {
            0
        } else {
            str_to_int(&s[0..last_idx])
        };
        let last = if s[last_idx] == '1' { 1 } else { 0 };
        2 * sub + last
    }
}

exec fn int_to_str(n: usize) -> (res: Vec<char>)
    ensures ValidBitString(res@),
        Str2Int(res@) == n
    decreases n
{
    if n == 0 {
        vec!['0']
    } else if n == 1 {
        vec!['1']
    } else {
        let mut res = int_to_str(n / 2);
        if n % 2 == 0 {
            res.push('0');
        } else {
            res.push('1');
        }
        res
    }
}

exec fn mod_exp_helper(base: usize, exp: usize, modulus: usize) -> (res: usize)
    requires modulus > 1,
        exp >= 0
    ensures res == Exp_int(base as nat, exp as nat) % (modulus as nat)
    decreases exp
{
    if exp == 0 {
        proof { lemma_exp_zero(base as nat); }
        1 % modulus
    } else {
        let half_exp = exp / 2;
        let half_result = mod_exp_helper(base, half_exp, modulus);
        let squared = (half_result * half_result) % modulus;
        
        if exp % 2 == 0 {
            squared
        } else {
            (squared * (base % modulus)) % modulus
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): implementation calling helper functions */
    let x = str_to_int(sx);
    let y = str_to_int(sy);
    let z = str_to_int(sz);
    
    let result_int = mod_exp_helper(x, y, z);
    let result = int_to_str(result_int);
    
    result
}
// </vc-code>

fn main() {}
}


