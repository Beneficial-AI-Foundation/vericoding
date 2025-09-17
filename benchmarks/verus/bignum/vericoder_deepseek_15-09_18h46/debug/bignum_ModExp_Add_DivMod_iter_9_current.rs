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
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
fn add_helper(a: char, b: char, carry: char) -> (char, char) {
    let ones = (if a == '1' { 1 } else { 0 }) + (if b == '1' { 1 } else { 0 }) + (if carry == '1' { 1 } else { 0 });
    match ones {
        0 => ('0', '0'),
        1 => ('1', '0'),
        2 => ('0', '1'),
        _ => ('1', '1'),
    }
}
// </vc-code>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): Add function body with proper initialization and loop */
{
    let mut i = dividend.len() as int - 1;
    let mut q = Vec::new();
    let mut r = Vec::new();
    
    while i >= 0
        invariant
            ValidBitString(q@),
            ValidBitString(r@)
    {
        r.insert(0, dividend[i as usize]);
        
        if Str2Int(r@) >= Str2Int(divisor@) {
            let mut temp_r = r@;
            let mut count = 0;
            while Str2Int(temp_r) >= Str2Int(divisor@)
                invariant
                    ValidBitString(temp_r),
                    count >= 0
            {
                temp_r = Str2Int(temp_r) - Str2Int(divisor@);
                count += 1;
            }
            q.push(if count > 0 { '1' } else { '0' });
            r = temp_r.to_string().chars().collect();
        } else {
            q.push('0');
        }
        
        i -= 1;
    }
    
    (q, r)
}
// </vc-code>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): Modular exponentiation implementation using repeated squaring */
{
    let mut base = sx.to_vec();
    let mut result = vec!['1'];
    
    let mut exp = sy.to_vec();
    
    while !exp.is_empty()
        invariant
            ValidBitString(result@),
            ValidBitString(base@),
            Str2Int(result@) == Exp_int(Str2Int(sx@), Str2Int(result.len())) % Str2Int(sz@)
    {
        if exp[exp.len() - 1] == '1' {
            let (product, _) = Mul(&result, &base);
            let (_, remainder) = DivMod(&product, sz);
            result = remainder;
        }
        
        let (square, _) = Mul(&base, &base);
        let (_, base_remainder) = DivMod(&square, sz);
        base = base_remainder;
        
        exp.pop();
    }
    
    result
}
// </vc-code>

fn main() {}
}


