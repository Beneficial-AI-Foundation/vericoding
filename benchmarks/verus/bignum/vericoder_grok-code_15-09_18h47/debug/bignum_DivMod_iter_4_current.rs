
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
spec fn Int2Str(n: nat) -> Seq<char>
  ensures
    ValidBitString(result),
    Str2Int(result) == n,
  decreases n
{
  if n == 0 {
    seq!['0']
  } else {
    let prefix = Int2Str(n / 2);
    prefix.push(if n % 2 == 0 { '0' } else { '1' })
  }
}

exec fn ExecStr2Int(s: &[char]) -> (res: nat)
  requires
    ValidBitString(s@),
  ensures
    res == Str2Int(s@),
  decreases s.len()
{
  if s.is_empty() {
    0nat
  } else if s[s.len() - 1] == '1' {
    2 * ExecStr2Int(&s[0..s.len() - 1]) + 1nat
  } else {
    2 * ExecStr2Int(&s[0..s.len() - 1]) + 0nat
  }
}

/* helper modified by LLM (iteration 2): fixed use of int in exec code by using ghost variables */
exec fn Seq_to_Vec(s: Seq<char>) -> (res: Vec<char>)
  ensures
    res@ == s,
  decreases s.len()
{
  if s.len() == 0 {
    Vec::new()
  } else {
    let ghost len = s.len();
    let ghost end = len - 1;
    let mut res = Seq_to_Vec(s.subrange(0, end));
    res.push(s.index(end));
    res
  }
}

/* helper modified by LLM (iteration 4): added exec Int2Str to convert nat to Vec<char> */
exec fn ExecInt2Str(n: nat) -> (res: Vec<char>)
  ensures
    ValidBitString(res@),
    Str2Int(res@) == n,
  decreases n
{
  if n == 0 {
    vec!['0']
  } else {
    let mut prefix = ExecInt2Str(n / 2);
    let digit = if n % 2 == 0 { '0' } else { '1' };
    prefix.push(digit);
    prefix
  }
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): used ExecInt2Str for direct Vec conversion */
{
    let dividend_val = ExecStr2Int(dividend);
    let divisor_val = ExecStr2Int(divisor);
    let quotient_val = dividend_val / divisor_val;
    let remainder_val = dividend_val % divisor_val;
    let quotient_vec = ExecInt2Str(quotient_val);
    let remainder_vec = ExecInt2Str(remainder_val);
    return (quotient_vec, remainder_vec);
}
// </vc-code>

fn main() {}
}


