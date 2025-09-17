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
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* helper modified by LLM (iteration 2): Added ModExp helper function */
exec fn ModExp(base: &[char], exp: &[char], modulus: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(base@),
        ValidBitString(exp@),
        ValidBitString(modulus@),
        Str2Int(modulus@) > 1
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Exp_int(Str2Int(base@), Str2Int(exp@)) % Str2Int(modulus@)
{
    if exp.len() == 0 || (exp.len() == 1 && exp[0] == '0') {
        return vec!['1'];
    }
    
    let mut result = vec!['1'];
    let mut base_mod = base.to_vec();
    let mut i = 0;
    
    while i < exp.len()
        invariant
            i <= exp.len(),
            ValidBitString(result@),
            ValidBitString(base_mod@)
    {
        if exp[exp.len() - 1 - i] == '1' {
            let temp = Mul(&result, &base_mod);
            result = simple_mod(&temp, modulus);
        }
        
        if i + 1 < exp.len() {
            let squared = Mul(&base_mod, &base_mod);
            base_mod = simple_mod(&squared, modulus);
        }
        
        i += 1;
    }
    
    result
}

/* helper modified by LLM (iteration 2): Added simple modulo helper */
exec fn simple_mod(dividend: &[char], divisor: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(dividend@),
        ValidBitString(divisor@),
        Str2Int(divisor@) > 0
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(dividend@) % Str2Int(divisor@)
{
    if compare_bit_strings(dividend, divisor) < 0 {
        return dividend.to_vec();
    }
    
    let mut result = dividend.to_vec();
    
    while compare_bit_strings(&result, divisor) >= 0
        invariant
            ValidBitString(result@)
    {
        result = subtract_bit_strings(&result, divisor);
    }
    
    result
}

/* helper modified by LLM (iteration 2): Added bit string comparison */
exec fn compare_bit_strings(s1: &[char], s2: &[char]) -> (res: i32)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@)
    ensures
        (res < 0) == (Str2Int(s1@) < Str2Int(s2@)),
        (res == 0) == (Str2Int(s1@) == Str2Int(s2@)),
        (res > 0) == (Str2Int(s1@) > Str2Int(s2@))
{
    if s1.len() < s2.len() { return -1; }
    if s1.len() > s2.len() { return 1; }
    
    let mut i = 0;
    while i < s1.len()
        invariant
            i <= s1.len(),
            s1.len() == s2.len()
    {
        if s1[i] < s2[i] { return -1; }
        if s1[i] > s2[i] { return 1; }
        i += 1;
    }
    
    0
}

/* helper modified by LLM (iteration 2): Added bit string subtraction */
exec fn subtract_bit_strings(s1: &[char], s2: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
        Str2Int(s1@) >= Str2Int(s2@)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
{
    let mut result = vec!['0'; s1.len()];
    let mut borrow = 0;
    let mut i = s1.len();
    
    while i > 0
        invariant
            i <= s1.len(),
            result.len() == s1.len(),
            ValidBitString(result@)
    {
        i -= 1;
        let digit1 = if s1[i] == '1' { 1 } else { 0 };
        let digit2 = if i < s2.len() && s2[i] == '1' { 1 } else { 0 };
        
        let diff = digit1 - digit2 - borrow;
        
        if diff >= 0 {
            result[i] = if diff == 1 { '1' } else { '0' };
            borrow = 0;
        } else {
            result[i] = '1';
            borrow = 1;
        }
    }
    
    remove_leading_zeros(&result)
}

/* helper modified by LLM (iteration 2): Added leading zero removal */
exec fn remove_leading_zeros(s: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s@)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s@)
{
    let mut start = 0;
    while start < s.len() && s[start] == '0'
        invariant
            start <= s.len()
    {
        start += 1;
    }
    
    if start == s.len() {
        vec!['0']
    } else {
        s[start..].to_vec()
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
/* code modified by LLM (iteration 2): Fixed type casting and function calls */
{
    if ghost(Str2Int(sy@)) == 0 {
        return vec!['1'];
    }
    
    if n == 0 {
        if sy[0] == '1' {
            let x_mod_z = ModExp(sx, &vec!['1'], sz);
            return x_mod_z;
        } else {
            return vec!['1'];
        }
    }
    
    let sy_half_seq = sy@.subrange(1, sy@.len());
    let mut sy_half_vec = Vec::new();
    let mut i = 0;
    
    while i < sy_half_seq.len()
        invariant
            i <= sy_half_seq.len(),
            sy_half_vec.len() == i,
            ValidBitString(sy_half_vec@)
    {
        sy_half_vec.push(sy_half_seq[i as int]);
        i += 1;
    }
    
    let temp = ModExpPow2(sx, &sy_half_vec, n - 1, sz);
    let squared = Mul(&temp, &temp);
    let squared_mod = ModExp(&squared, &vec!['1'], sz);
    
    if sy[0] == '1' {
        let x_mod = ModExp(sx, &vec!['1'], sz);
        let final_result = Mul(&squared_mod, &x_mod);
        ModExp(&final_result, &vec!['1'], sz)
    } else {
        squared_mod
    }
}
// </vc-code>

fn main() {}
}


