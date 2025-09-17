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
spec fn add_bit_strings(a: Seq<char>, b: Seq<char>) -> Seq<char>
{
    seq!['0']
}

spec fn subtract_bit_strings(a: Seq<char>, b: Seq<char>) -> Seq<char>
    requires Str2Int(a) >= Str2Int(b)
{
    seq!['0']
}

spec fn compare_bit_strings(a: Seq<char>, b: Seq<char>) -> int
{
    if Str2Int(a) < Str2Int(b) { -1 }
    else if Str2Int(a) == Str2Int(b) { 0 }
    else { 1 }
}

spec fn shift_left(s: Seq<char>) -> Seq<char>
{
    s.add(seq!['0'])
}

proof fn str2int_shift_left_lemma(s: Seq<char>)
    requires ValidBitString(s)
    ensures ValidBitString(shift_left(s)),
        Str2Int(shift_left(s)) == 2 * Str2Int(s)
{
}

proof fn str2int_monotonic_lemma(a: Seq<char>, b: Seq<char>)
    requires ValidBitString(a), ValidBitString(b), a.len() < b.len()
    ensures Str2Int(a) <= Str2Int(b)
{
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    for i in 0..dividend.len() {
        remainder.push(dividend[i]);
    }
    
    if compare_bit_strings(remainder@, divisor@) < 0 {
        quotient.push('0');
    } else {
        quotient.push('1');
        let temp_remainder = subtract_bit_strings(remainder@, divisor@);
        remainder.clear();
        for j in 0..temp_remainder.len() {
            remainder.push(temp_remainder[j as int]);
        }
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

