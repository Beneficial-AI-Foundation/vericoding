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
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fix type errors and implementation issues */
    let x_seq = sx@;
    let y_seq = sy@;
    let z_seq = sz@;
    let modulus = Str2Int(z_seq) as int;
    let base = (Str2Int(x_seq) as int) % modulus;
    let mut result: int = 1;
    let mut current: int = base;
    let mut exp: int = Str2Int(y_seq) as int;
    
    while exp > 0
        invariant
            exp >= 0,
            result >= 1,
            current >= 1,
            (Exp_int(base as nat, exp as nat) as int) * result % modulus == Exp_int(Str2Int(x_seq), Str2Int(y_seq)) as int % modulus,
        decreases exp
    {
        if exp % 2 == 1 {
            result = (result * current) % modulus;
        }
        current = (current * current) % modulus;
        exp = exp / 2;
    }
    
    let mut res_vec = Vec::new();
    let mut temp = result;
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
    
    res_vec.reverse();
    res_vec
}
// </vc-code>

fn main() {}
}
