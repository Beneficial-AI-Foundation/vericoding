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
/* helper modified by LLM (iteration 10): fixed nat literal syntax errors */
spec fn exp_mod(base: nat, exp: nat, modulus: nat) -> nat
    requires modulus > 1
    decreases exp
{
    if exp == 0 {
        1 % modulus
    } else if exp % 2 == 0 {
        let half_exp = exp_mod(base, exp / 2, modulus);
        (half_exp * half_exp) % modulus
    } else {
        (base * exp_mod(base, (exp - 1) as nat, modulus)) % modulus
    }
}

proof fn lemma_exp_mod_correctness(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures exp_mod(base, exp, modulus) == Exp_int(base, exp) % modulus
    decreases exp
{
}

exec fn nat_to_bit_string(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@),
            Str2Int(result@) == n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut num = n;
        while num > 0
            invariant ValidBitString(result@)
        {
            if num % 2 == 0 {
                result.push('0');
            } else {
                result.push('1');
            }
            num = num / 2;
        }
        result.reverse();
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Add_Zeroes_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): fixed nat literal syntax errors */
    let base = Str2Int(sx@);
    let exp = Str2Int(sy@);
    let modulus = Str2Int(sz@);
    
    let result_nat = exp_mod(base, exp, modulus);
    
    proof {
        lemma_exp_mod_correctness(base, exp, modulus);
    }
    
    nat_to_bit_string(result_nat)
}
// </vc-code>

fn main() {}
}
