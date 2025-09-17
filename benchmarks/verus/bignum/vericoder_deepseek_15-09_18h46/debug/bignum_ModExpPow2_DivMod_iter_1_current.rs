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
{
    let mut q = Vec::new();
    let mut r = Vec::new();
    let mut current = Vec::new();
    let divisor_val = Str2Int(divisor@);
    
    for i in 0..dividend.len() {
        current.push(dividend[i as usize]);
        let current_val = Str2Int(current@);
        
        if current_val >= divisor_val {
            q.push('1');
            let remainder_val = current_val % divisor_val;
            current = Int2Vec(remainder_val);
        } else {
            q.push('0');
        }
    }
    
    (q, current)
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
{
    proof {
        lemma_exp_mod_pow2_property();
    }
    
    if n == 0 {
        let base = Str2Int(sx@);
        let exponent = Str2Int(sy@);
        let modulus = Str2Int(sz@);
        let result_val = if exponent == 0 { 1 } else { base } % modulus;
        return Int2Vec(result_val);
    }
    
    let half_n = n - 1;
    let mut half_sy = Vec::new();
    for i in 0..half_n {
        half_sy.push(sy[i as usize]);
    }
    
    let half_result = ModExpPow2(sx, &half_sy, half_n, sz);
    let half_val = Str2Int(half_result@);
    
    let squared_val = (half_val * half_val) % Str2Int(sz@);
    
    if sy[n as usize] == '1' {
        let base_val = Str2Int(sx@);
        let result_val = (squared_val * base_val) % Str2Int(sz@);
        Int2Vec(result_val)
    } else {
        Int2Vec(squared_val)
    }
}
// </vc-code>

fn main() {}
}


