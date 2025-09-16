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
/* helper modified by LLM (iteration 10): added exec function to convert Str2Int result to u64 */
spec fn ModExp_Helper(base: nat, exp: nat, modulus: nat) -> nat
    decreases exp
{
    if exp == 0 { 1nat % modulus }
    else if exp % 2 == 0 {
        let half_exp = ModExp_Helper(base, exp / 2, modulus);
        (half_exp * half_exp) % modulus
    } else {
        (base * ModExp_Helper(base, (exp - 1) as nat, modulus)) % modulus
    }
}

proof fn lemma_mod_exp_correct(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures ModExp_Helper(base, exp, modulus) == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
    } else if exp % 2 == 0 {
        lemma_mod_exp_correct(base, exp / 2, modulus);
    } else {
        lemma_mod_exp_correct(base, (exp - 1) as nat, modulus);
    }
}

exec fn str2int_exec(s: &[char]) -> (result: u64)
    requires ValidBitString(s@)
{
    let mut result: u64 = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            ValidBitString(s@)
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

exec fn nat_to_bit_string(n: u64) -> (result: Vec<char>)
    ensures ValidBitString(result@)
{
    let mut result = Vec::new();
    let mut temp = n;
    
    if temp == 0 {
        result.push('0');
    } else {
        while temp > 0
            invariant
                ValidBitString(result@)
            decreases temp
        {
            if temp % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            temp = temp / 2;
        }
        // Create a new vector in reverse order instead of reversing in place
        let mut reversed = Vec::new();
        let len = result.len();
        let mut i = 0;
        while i < len
            invariant
                i <= len,
                ValidBitString(reversed@)
            decreases len - i
        {
            reversed.push(result[len - 1 - i]);
            i = i + 1;
        }
        result = reversed;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): added decreases clause to while loop */
{
    proof {
        lemma_mod_exp_correct(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
    }
    
    let base_val = str2int_exec(sx);
    let exp_val = str2int_exec(sy);
    let mod_val = str2int_exec(sz);
    
    // Simple modular exponentiation implementation
    let mut result: u64 = 1;
    let mut base = base_val % mod_val;
    let mut exp = exp_val;
    
    while exp > 0
        invariant
            mod_val > 1
        decreases exp
    {
        if exp % 2 == 1 {
            result = (result * base) % mod_val;
        }
        base = (base * base) % mod_val;
        exp = exp / 2;
    }
    
    nat_to_bit_string(result)
}
// </vc-code>

fn main() {}
}
