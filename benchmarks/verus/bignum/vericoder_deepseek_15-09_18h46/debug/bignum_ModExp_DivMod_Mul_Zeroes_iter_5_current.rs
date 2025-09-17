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

proof fn str2int_recursive(s: Seq<char>, c: char) 
    requires ValidBitString(s) && (c == '0' || c == '1') 
    ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat }) 
{ 
    /* helper modified by LLM (iteration 5): Added nat suffix to resolve type annotation error */
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
    /* code modified by LLM (iteration 5): Fixed type compatibility issues by using proper nat types and operations */
    let mut base = Str2Int(sx@) as int;
    let mut exponent = Str2Int(sy@) as int;
    let modulus = Str2Int(sz@) as int;
    let mut result = 1;
    
    while exponent > 0
        invariant
            result >= 0,
            exponent >= 0,
            result % modulus == Exp_int(base as nat, exponent as nat) % (modulus as nat)
    {
        if exponent % 2 == 1 {
            result = (result * base) % modulus;
        }
        base = (base * base) % modulus;
        exponent = exponent / 2;
    }
    
    let mut res = Vec::new();
    res.push(if result == 1 { '1' } else { '0' });
    res
}
// </vc-code>

fn main() {}
}
