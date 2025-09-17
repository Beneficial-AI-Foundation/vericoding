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
proof fn exp_int_lemma_1(x: nat, y: nat) 
    requires
        y > 0,
    ensures
        Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
}

proof fn exp_int_lemma_2(x: nat, y: nat) 
    ensures
        Exp_int(x, y) >= 1
{
}

proof fn str2int_lemma_1(s: Seq<char>, c: char) 
    requires
        ValidBitString(s.push(c)),
    ensures
        Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1 } else { 0 })
{
}

proof fn str2int_lemma_2(s: Seq<char>) 
    requires
        ValidBitString(s),
    ensures
        Str2Int(s) >= 0
{
}

proof fn valid_bitstring_lemma_1(s: Seq<char>, i: int) 
    requires
        ValidBitString(s),
        0 <= i && i < s.len(),
    ensures
        s[i] == '0' || s[i] == '1'
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
    let mut x = sx.to_seq().clone();
    let mut y = sy.to_seq().clone();
    let z = sz.to_seq().clone();
    let modulus = Str2Int(z);
    let base = Str2Int(x) % modulus;
    let mut result = 1;
    let mut current = base;
    let mut exp = Str2Int(y);
    
    proof {
        exp_int_lemma_2(base, exp);
        str2int_lemma_2(x);
        str2int_lemma_2(y);
        str2int_lemma_2(z);
    }
    
    while exp > 0
        invariant
            exp >= 0,
            result >= 1,
            current >= 1,
            Exp_int(base, exp as nat) * result % modulus == Exp_int(Str2Int(sx@), Str2Int(y@)) % modulus,
        decreases exp
    {
        if exp % 2 == 1 {
            result = (result * current) % modulus;
        }
        current = (current * current) % modulus;
        exp = exp / 2;
        
        proof {
            exp_int_lemma_1(base, exp as nat);
        }
    }
    
    let res_vec = Vec::new();
    // Convert result to binary representation
    let mut temp = result;
    while temp > 0
        invariant
            temp >= 0,
            ValidBitString(res_vec@),
            Str2Int(res_vec@) == result - temp * Exp_int(2, res_vec@.len() as nat),
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
