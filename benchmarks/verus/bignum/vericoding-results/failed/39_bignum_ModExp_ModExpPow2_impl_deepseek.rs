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
/* helper modified by LLM (iteration 10): Fix type conversion functions using proper Verus syntax and typing */
proof fn str2int_lemma_1(s: Seq<char>, c: char) 
    requires
        ValidBitString(s.push(c)),
    ensures
        Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })
{
}

proof fn exp_int_lemma_2(x: nat, y: nat) 
    ensures
        Exp_int(x, y) >= 1nat
{
}

exec fn to_exec_int(n: nat) -> (res: int)
    ensures res == n as int
{
    let mut res: int = 0;
    let mut temp: nat = n;
    
    while temp > 0
        invariant
            temp >= 0,
            res == (n - temp) as int,
        decreases temp
    {
        res = res + 1;
        temp = temp - 1;
    }
    res
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fix type mismatches by converting nat to int properly */
{
    let x_nat = Str2Int(sx@);
    let y_nat = Str2Int(sy@);
    let z_nat = Str2Int(sz@);
    
    let x_int: int = to_exec_int(x_nat);
    let y_int: int = to_exec_int(y_nat);
    let z_int: int = to_exec_int(z_nat);
    let modulus: int = z_int;
    let base: int = x_int % modulus;
    let mut result: int = 1;
    let mut current: int = base;
    let mut exp: int = y_int;
    
    while exp > 0
        invariant
            exp >= 0,
            result >= 1,
            current >= 1,
            (Exp_int(base as nat, exp as nat) as int) * result % modulus == Exp_int(Str2Int(sx@), Str2Int(sy@)) as int % modulus,
        decreases exp
    {
        if exp % 2 == 1 {
            result = (result * current) % modulus;
        }
        current = (current * current) % modulus;
        exp = exp / 2;
    }
    
    let mut res_vec = Vec::new();
    let mut temp: int = result;
    while temp > 0
        invariant
            temp >= 0,
            ValidBitString(res_vec@),
            Str2Int(res_vec@) == (result - temp * Exp_int(2, res_vec@.len() as nat) as int) as nat,
        decreases temp
    {
        let bit = if temp % 2 == 1 { '1' } else { '0' };
        res_vec.push(bit);
        temp = temp / 2;
    }
    
    if res_vec.len() == 0 {
        res_vec.push('0');
    } else {
        res_vec.reverse();
    }
    res_vec
}
// </vc-code>

fn main() {}
}
