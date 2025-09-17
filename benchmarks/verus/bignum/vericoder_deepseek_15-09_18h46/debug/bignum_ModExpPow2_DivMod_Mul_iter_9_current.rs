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
proof fn divmod_lemma(x: nat, y: nat) {
    if y > 0 {
        assert(x / y == x / y);
        assert(x % y == x % y);
    }
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): Implement DivMod with binary division algorithm */
{
    let d_len = divisor.len();
    let mut rem = dividend.to_vec();
    let mut quo = Vec::new();
    let divisor_val = Str2Int(divisor@);
    
    if Str2Int(dividend@) < divisor_val {
        return (Vec::from(['0']), dividend.to_vec());
    }
    
    let mut current = 0;
    let mut i = 0;
    while i < rem.len() {
        current = current * 2 + (if rem[i] == '1' { 1 } else { 0 });
        if current >= divisor_val {
            quo.push('1');
            current = current - divisor_val;
        } else {
            quo.push('0');
        }
        i += 1;
    }
    
    let mut remainder_bits = Vec::new();
    if current > 0 {
        let mut temp = current;
        while temp > 0 {
            remainder_bits.push(if temp % 2 == 1 { '1' } else { '0' });
            temp = temp / 2;
        }
        remainder_bits.reverse();
    } else {
        remainder_bits.push('0');
    }
    
    (Vec::from(quo), remainder_bits)
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
/* code modified by LLM (iteration 9): Fix modular exponentiation using proper base-2 exponent handling */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    if y_val == 0 {
        return Vec::from(['1']);
    }
    
    let mut result = 1 % z_val;
    let mut base = x_val % z_val;
    let mut exponent = y_val;
    
    while exponent > 0 {
        invariant
            result * Exp_int(base, exponent) % z_val == Exp_int(x_val, y_val) % z_val,
        decreases exponent,
        {
            if exponent % 2 == 1 {
                result = (result * base) % z_val;
            }
            base = (base * base) % z_val;
            exponent = exponent / 2;
        }
    }
    
    let mut res_vec = Vec::new();
    if result == 0 {
        res_vec.push('0');
    } else {
        let mut temp = result;
        while temp > 0 {
            res_vec.push(if temp % 2 == 1 { '1' } else { '0' });
            temp = temp / 2;
        }
        res_vec.reverse();
    }
    res_vec
}
// </vc-code>

fn main() {}
}
