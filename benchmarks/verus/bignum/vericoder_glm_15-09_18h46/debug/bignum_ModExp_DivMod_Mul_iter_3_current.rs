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
/* helper modified by LLM (iteration 3): fixed nat literals and indexing issues */
exec fn str_to_int(s: &[char]) -> (result: nat)
    requires ValidBitString(s@)
    ensures result == Str2Int(s@)
{
    let mut res = 0 as nat;
    let mut i: usize = 0;
    while i < s.len()
        invariant 0 <= i as int <= s.len() as int,
                res == Str2Int(s@.subrange(0, i as int))
    {
        if s[i] == '1' {
            res = (res * 2 + 1) as nat;
        } else {
            res = (res * 2) as nat;
        }
        i += 1;
    }
    res
}

/* helper modified by LLM (iteration 3): fixed nat literals and type casting */
exec fn int_to_str(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@), Str2Int(result@) == n
{
    if n == 0 {
        return vec!['0'];
    }
    
    let mut res = Vec::new();
    let mut num = n;
    let mut power = 1 as nat;
    
    while num > 0
        invariant num >= 0,
                Str2Int(res@.reverse()) + num * power == n
        decreases num
    {
        let bit = num % (2 as nat);
        if bit == 0 {
            res.push('0');
        } else {
            res.push('1');
        }
        num = num / (2 as nat);
        power = power * (2 as nat);
    }
    res.reverse();
    res
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed nat literals and type casting throughout */
    // Convert input strings to integers
    let x = str_to_int(sx);
    let y = str_to_int(sy);
    let z = str_to_int(sz);
    
    // Implement modular exponentiation using square-and-multiply algorithm
    let mut result = 1 as nat;
    let mut current_base = (x % z) as nat;
    let mut remaining_exp = y;
    
    while remaining_exp > 0
        invariant remaining_exp >= 0,
                result * Exp_int(current_base, remaining_exp) % z == Exp_int(x % z, y) % z
        decreases remaining_exp
    {
        if remaining_exp % (2 as nat) == 1 {
            result = (result * current_base) % z;
        }
        current_base = (current_base * current_base) % z;
        remaining_exp = remaining_exp / (2 as nat);
    }
    
    // Convert the result back to a bit string
    int_to_str(result)
}
// </vc-code>

fn main() {}
}
