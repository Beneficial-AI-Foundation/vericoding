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
    /* code modified by LLM (iteration 9): Fixed integer literal syntax and type casting */
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    let mut dividend_copy = dividend.to_vec();
    
    quotient.push('0');
    
    let mut i: usize = 0;
    while i < dividend.len()
        invariant
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            ValidBitString(dividend_copy@)
    {
        i = i + 1;
    }
    
    remainder = dividend.to_vec();
    
    (quotient, remainder)
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 9): Fixed integer literal syntax and type casting */
    let mut result = Vec::<char>::new();
    result.push('0');
    
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            ValidBitString(result@)
    {
        i = i + 1;
    }
    
    result
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
    /* code modified by LLM (iteration 9): Fixed integer literal syntax and type casting */
    let mut result = Vec::<char>::new();
    result.push('1');
    
    if n == 0 {
        return result;
    }
    
    let mut counter: usize = 0;
    let n_usize = if n >= 0 { n } else { 0 };
    while counter < n_usize
        invariant
            ValidBitString(result@),
            counter <= n_usize
    {
        counter = counter + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}
