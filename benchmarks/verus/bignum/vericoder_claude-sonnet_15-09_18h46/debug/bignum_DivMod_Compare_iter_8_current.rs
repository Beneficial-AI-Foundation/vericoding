use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 8): Fixed nat literal operations with proper casting */
exec fn str_to_vec(s: &[char]) -> (res: Vec<char>)
    ensures res@ == s@
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result@ == s@.subrange(0, i as int),
    {
        result.push(s[i]);
        i += 1;
    }
    result
}

exec fn vec_to_nat(v: &Vec<char>) -> (res: nat)
    requires ValidBitString(v@)
    ensures res == Str2Int(v@)
{
    let mut result: nat = 0nat;
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            ValidBitString(v@),
            result == Str2Int(v@.subrange(0, i as int)),
    {
        result = result * (2 as nat);
        if v[i] == '1' {
            result = result + (1 as nat);
        }
        i += 1;
    }
    result
}

exec fn nat_to_vec(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@)
{
    if n == (0 as nat) {
        let mut result = Vec::new();
        result.push('0');
        result
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        while temp > (0 as nat)
            invariant ValidBitString(result@)
        {
            if temp % (2 as nat) == (0 as nat) {
                result.push('0');
            } else {
                result.push('1');
            }
            temp = temp / (2 as nat);
        }
        result.reverse();
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 8): Fixed nat literal operations with proper casting */
    let dividend_val = vec_to_nat(&str_to_vec(dividend));
    let divisor_val = vec_to_nat(&str_to_vec(divisor));
    
    let quotient_val = dividend_val / divisor_val;
    let remainder_val = dividend_val % divisor_val;
    
    let quotient_vec = nat_to_vec(quotient_val);
    let remainder_vec = nat_to_vec(remainder_val);
    
    (quotient_vec, remainder_vec)
}
// </vc-code>

fn main() {}
}

