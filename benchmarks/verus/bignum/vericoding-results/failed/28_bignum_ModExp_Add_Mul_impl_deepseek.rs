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
fn binary_addition(a: &[char], b: &[char]) -> (carry: bool, sum: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@)
    ensures ValidBitString(sum@), sum@.len() == if carry { a@.len() + 1 } else { a@.len() },
        (if carry { Exp_int(2, a@.len() as nat) } else { 0 }) + Str2Int(sum@) == Str2Int(a@) + Str2Int(b@)
{
    let mut i = (a.len() as int - 1);
    let mut carry = false;
    let mut result = Vec::new();
    
    while i >= 0
        invariant
            -1 <= i && i < a.len() as int,
            ValidBitString(result@),
            result@.len() == (a.len() as int - i - 1) as nat,
            (if carry { Exp_int(2, result@.len() as nat) } else { 0 }) + Str2Int(result@) == 
                Str2Int(a@.subrange(i + 1, a.len() as int)) + Str2Int(b@.subrange(i + 1, b.len() as int))
        decreases i + 1
    {
        let bit_a = if a[i as usize] == '1' { 1 } else { 0 };
        let bit_b = if b[i as usize] == '1' { 1 } else { 0 };
        let sum_bits = bit_a + bit_b + (if carry { 1 } else { 0 });
        
        carry = sum_bits >= 2;
        let sum_bit = if sum_bits % 2 == 1 { '1' } else { '0' };
        
        result.push(sum_bit);
        i = i - 1;
    }
    
    if carry {
        result.push('1');
    }
    
    result.reverse();
    (carry, result)
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Complete binary multiplication implementation */
    let mut result = vec!['0'];
    let zero = vec!['0'];
    
    for i in 0..s1.len() {
        if s1[i] == '1' {
            let mut shifted = s2.to_vec();
            for _ in 0..i {
                shifted.push('0');
            }
            let (_, new_result) = binary_addition(&result, &shifted);
            result = new_result;
        }
    }
    
    result
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
{
    /* code modified by LLM (iteration 10): Fixed modular exponentiation implementation */
    let mut result = vec!['1'];
    let mut base = sx.to_vec();
    let mut exponent = sy.to_vec();
    
    while exponent.len() > 0 {
        if exponent[exponent.len() - 1] == '1' {
            let temp = Mul(&result, &base);
            let mod_temp = Add(&temp, &vec!['0']);
            result = mod_temp;
        }
        
        let squared = Mul(&base, &base);
        let mod_squared = Add(&squared, &vec!['0']);
        base = mod_squared;
        
        exponent.pop();
    }
    
    result
}
// </vc-code>

fn main() {}
}


