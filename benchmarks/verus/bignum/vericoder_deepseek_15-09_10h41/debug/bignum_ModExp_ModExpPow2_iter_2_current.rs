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
/* helper modified by LLM (iteration 2): Added nat conversion helpers and fix type issues */
proof fn lemma_nat_to_int_identity(n: nat)
    ensures n as int == n
{
}

proof fn lemma_nat_arithmetic()
{
}

proof fn lemma_mod_arithmetic(a: nat, b: nat, m: nat)
    requires m > 0
{
}

proof fn lemma_nat_division(n: nat, d: nat)
    requires d > 0
    ensures (n as int / d as int) as nat == n / d
{
}

proof fn lemma_nat_modulo(n: nat, d: nat)
    requires d > 0
    ensures (n as int % d as int) as nat == n % d
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
/* code modified by LLM (iteration 2): Fixed type mismatches and arithmetic operations */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    let mut result: nat = 1;
    let mut base: nat = x_val % z_val;
    let mut exponent: nat = y_val;
    
    while exponent > 0
        invariant
            result >= 0,
            base >= 0,
            exponent >= 0,
            Exp_int(x_val, y_val) % z_val == (result * Exp_int(base, exponent)) % z_val
        decreases exponent
    {
        proof { lemma_nat_modulo(exponent, 2); }
        if (exponent % 2) == 1 {
            proof { lemma_nat_arithmetic(); }
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        proof { lemma_nat_division(exponent, 2); }
        exponent = exponent / 2;
    }
    
    let mut res_vec = Vec::new();
    if result == 0 {
        res_vec.push('0');
    } else {
        let mut temp: nat = result;
        while temp > 0
            invariant
                temp >= 0
            decreases temp
        {
            proof { lemma_nat_modulo(temp, 2); }
            if (temp % 2) == 0 {
                res_vec.push('0');
            } else {
                res_vec.push('1');
            }
            proof { lemma_nat_division(temp, 2); }
            temp = temp / 2;
        }
        res_vec.reverse();
    }
    
    res_vec
}
// </vc-code>

fn main() {}
}
