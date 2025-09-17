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

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
proof fn lemma_div_remainder(a: nat, b: nat)
    requires
        b > 0
    ensures
        a % b < b
{
    // Fundamental property of modulo operation
}

proof fn lemma_div_mod_relation(a: nat, b: nat)
    requires
        b > 0
    ensures
        a == (a / b) * b + a % b
{
    // Division and modulo relationship
}

proof fn lemma_exp_mod_property(x: nat, y: nat, m: nat)
    requires
        m > 1
    ensures
        Exp_int(x, y) % m == if y == 0 { 1 % m } else { (x * (Exp_int(x, y - 1) % m)) % m }
{
    if y > 0 {
        lemma_exp_mod_property(x, y - 1, m);
    }
}

proof fn lemma_pow2_exp(n: nat)
    ensures
        Exp_int(2, n) >= 1
{
    if n > 0 {
        lemma_pow2_exp(n - 1);
    }
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Implement modular exponentiation using repeated squaring */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    let mut result: nat = 1 % z_val;
    let mut base: nat = x_val % z_val;
    let mut exp: nat = y_val;
    
    while exp > 0
        invariant
            (result * Exp_int(base, exp)) % z_val == Exp_int(x_val, y_val) % z_val,
            base < z_val,
            result < z_val
        decreases exp
    {
        proof {
            lemma_exp_mod_property(base, exp, z_val);
            lemma_div_mod_relation(exp, 2);
        }
        
        if exp % 2 == 1 {
            result = (result * base) % z_val;
        }
        
        base = (base * base) % z_val;
        exp = exp / 2;
    }
    
    int_to_bitstring(result)
}
// </vc-code>

fn main() {}
}


