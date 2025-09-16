
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
/* helper modified by LLM (iteration 4): added 'nat' suffixes and casts to fix type mismatches */
exec fn compute_str_to_int(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    let mut i: usize = 0;
    let mut val: nat = 0nat;
    while i < s.len()
        invariant
            ValidBitString(s@),
            i <= s.len(),
            val == Str2Int(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        val = val * (2 as nat) + (if s[i] == '1' { 1nat } else { 0nat });
        i = i + 1;
    }
    val
}

spec fn Int2Str(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 { seq!['0'] }
    else if n == 1 { seq!['1'] }
    else { Int2Str(n / 2).push(if n % 2 == 1 { '1' } else { '0' }) }
}

proof fn lemma_int_str_conversion(n: nat)
    ensures
        Str2Int(Int2Str(n)) == n,
        ValidBitString(Int2Str(n)),
    decreases n
{
    if n > 1 {
        lemma_int_str_conversion(n / 2);
    }
}

exec fn compute_int_to_str(n: nat) -> (res: Vec<char>)
    ensures
        Str2Int(res@) == n,
        ValidBitString(res@),
{
    lemma_int_str_conversion(n);
    if n == 0nat {
        let mut v = Vec::new();
        v.push('0');
        v
    } else if n == 1nat {
        let mut v = Vec::new();
        v.push('1');
        v
    } else {
        let mut prefix = compute_int_to_str(n / (2 as nat));
        prefix.push(if n % (2 as nat) == 1nat { '1' } else { '0' });
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
{
    /* code modified by LLM (iteration 4): no changes; compilation errors were in helper functions */
    let n_dividend = compute_str_to_int(dividend);
    let n_divisor = compute_str_to_int(divisor);

    let n_quotient = n_dividend / n_divisor;
    let n_remainder = n_dividend % n_divisor;

    let res_quotient = compute_int_to_str(n_quotient);
    let res_remainder = compute_int_to_str(n_remainder);

    (res_quotient, res_remainder)
}
// </vc-code>

fn main() {}
}


