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
/* helper modified by LLM (iteration 7): Fixed `Residue` helper to compile by removing the `result` keyword from the ensures clause and referring to the function return value implicitly. Simplified the body of `Residue` to use `Seq::new` and iterate for placing bits, making it self-contained. The `trim_leading_zeros` helper was also fixed to use the correct `result` keyword in its `ensures` clause and simplified its logic. */
spec fn LeStr(s1: Seq<char>, s2: Seq<char>) -> bool {
    if s1.len() < s2.len() { false }
    else if s1.len() > s2.len() { true }
    else { Str2Int(s1) <= Str2Int(s2) }
}

spec fn Residue(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
    recommends ValidBitString(s1), ValidBitString(s2),
               s1.len() == s2.len(), Str2Int(s1) >= Str2Int(s2)
    ensures ValidBitString(
            {
                let res = Str2Int(s1) - Str2Int(s2);
                if res == 0 && s1.len() == 0 { Seq::empty() }
                else if res == 0 && s1.len() > 0 { Seq::new(s1.len(), |j| '0') }
                else {
                    let mut temp = res;
                    let mut bits = Seq::new(s1.len() as int, |j| '0');
                    let mut k = s1.len() as int - 1;
                    while k >= 0
                        invariant
                            k >= -1,
                            temp <= res,
                            temp >= 0,
                            bits.len() == s1.len() as int
                        decreases k
                    {
                        bits = bits.update(k, if temp % 2 == 1 { '1' } else { '0' });
                        temp = temp / 2;
                        k = k - 1;
                    }
                    bits
                }
            }
        ),
            Str2Int(Residue(s1, s2)) == Str2Int(s1) - Str2Int(s2)
{
    let sub_val = Str2Int(s1) - Str2Int(s2);
    let len = s1.len();
    if len == 0 {
        Seq::empty()
    } else {
        let mut res = Seq::new(len as int, |i: int| '0');
        let mut temp = sub_val;
        let mut i = len as int - 1;
        while i >= 0
            invariant
                i >= -1,
                temp >= 0,
                temp < (1_nat << (i + 1)),
                res.len() == len as int
            decreases i
        {
            res = res.update(i, if (temp % 2) == 1 { '1' } else { '0' });
            temp = temp / 2;
            i = i - 1;
        }
        res
    }
}

spec fn trim_leading_zeros(s: Seq<char>) -> Seq<char>
    ensures ValidBitString(trim_leading_zeros(s)),
            Str2Int(trim_leading_zeros(s)) == Str2Int(s),
            trim_leading_zeros(s).len() == 1 || trim_leading_zeros(s).len() == 0 || trim_leading_zeros(s).index(0) == '1'
{
    if s.len() == 0 {
        Seq::empty()
    } else if s.len() == 1 {
        s
    } else if s.index(0) == '0' {
        trim_leading_zeros(s.subrange(1, s.len() as int))
    } else {
        s
    }
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): Fixed `result` compilation errors for ensures clause by explicitly calling `Str2Int` on `res.0@` and `res.1@`. Also, `quotient_vec` and `remainder_vec` are converted to `Seq` before being passed to helper functions. */
{
    let s_dividend_seq = Seq::new(dividend.len(), |i| dividend[i]);
    let s_divisor_seq = Seq::new(divisor.len(), |i| divisor[i]);

    let mut quotient_vec: Vec<char> = Vec::<char>::new();
    let mut remainder_vec: Vec<char> = Vec::<char>::new();
    let mut i: usize = 0;

    while i < s_dividend_seq.len()
        invariant 
            0 <= i && i <= s_dividend_seq.len(),
            ValidBitString(s_dividend_seq),
            ValidBitString(s_divisor_seq),
            ValidBitString(quotient_vec@),
            ValidBitString(remainder_vec@),
            Str2Int(s_divisor_seq) > 0,
            remainder_vec.len() <= s_divisor_seq.len() + 1 // Remainder can grow by one digit
        decreases (s_dividend_seq.len() - i)
    {
        remainder_vec.push(s_dividend_seq@[i]);

        // Trim leading zeros from remainder_vec, if any
        let current_remainder_seq = trim_leading_zeros(remainder_vec@);
        remainder_vec = Vec::from_seq(current_remainder_seq);

        if remainder_vec.len() >= s_divisor_seq.len() && LeStr(remainder_vec@, s_divisor_seq) {
            let sub_res_seq = Residue(remainder_vec@, s_divisor_seq);
            remainder_vec = Vec::from_seq(sub_res_seq);
            quotient_vec.push('1');
        } else {
            quotient_vec.push('0');
        }
        i = i + 1;
    }

    let final_quotient_seq = trim_leading_zeros(quotient_vec@);
    let final_remainder_seq = trim_leading_zeros(remainder_vec@);

    (Vec::from_seq(final_quotient_seq), Vec::from_seq(final_remainder_seq))
}
// </vc-code>

fn main() {}
}

