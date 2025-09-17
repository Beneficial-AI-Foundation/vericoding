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
exec fn Str2Int_exec(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    let mut total: nat = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            ValidBitString(s@),
            total == Str2Int(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        total = total * 2;
        if s[i] == '1' {
            total = total + 1;
        }
        i = i + 1;
    }
    total
}

/* helper modified by LLM (iteration 5): fixed spec clause order */
exec fn Int2Str_exec(n: nat) -> (res: Vec<char>)
    ensures
        Str2Int(res@) == n,
        ValidBitString(res@),
    decreases n
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        return v;
    }

    let rem = n % 2;
    let quot = n / 2;
    
    let mut res = if quot == 0 {
        Vec::new()
    } else {
        Int2Str_exec(quot)
    };

    if rem == 1 {
        res.push('1');
    } else {
        res.push('0');
    }
    res
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
    /* code modified by LLM (iteration 5): Updated iteration comment as logic remains sound. */
    let dividend_val = Str2Int_exec(dividend);
    let divisor_val = Str2Int_exec(divisor);

    let quotient_val = dividend_val / divisor_val;
    let remainder_val = dividend_val % divisor_val;

    let quotient_vec = Int2Str_exec(quotient_val);
    let remainder_vec = Int2Str_exec(remainder_val);

    (quotient_vec, remainder_vec)
}
// </vc-code>

fn main() {}
}

