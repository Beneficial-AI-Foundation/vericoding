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
/* helper modified by LLM (iteration 8): Fix sequence indexing and type conversion helpers */
spec fn decimal_to_bitstring(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 {
    Seq::empty()
  } else {
    let digit = if n % 2 == 1 { '1' } else { '0' };
    decimal_to_bitstring(n / 2).push(digit)
  }
}

proof fn Str2Int_monotonic(s: Seq<char>, t: Seq<char>)
    requires ValidBitString(s), ValidBitString(t), s.len() <= t.len()
    ensures Str2Int(s) <= Str2Int(t)
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        let t_prefix = t.subrange(0, t.len() as int - 1);
        Str2Int_monotonic(s_prefix, t_prefix);
    }
}

proof fn Str2Int_append(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })
    decreases s.len()
{
}

proof fn Str2Int_zero()
    ensures Str2Int(Seq::empty()) == 0
{
}

spec fn bitstring_lt(s1: Seq<char>, s2: Seq<char>) -> bool
    recommends ValidBitString(s1), ValidBitString(s2)
{
    s1.len() < s2.len() || (s1.len() == s2.len() && Str2Int(s1) < Str2Int(s2))
}

spec fn seq_at_index(s: Seq<char>, idx: usize) -> char
    requires idx < s.len()
{
    s.index(idx as int)
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
/* code modified by LLM (iteration 8): Fix sequence indexing with proper type conversion */
{
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    
    let mut i: usize = 0;
    while i < dividend.len()
        invariant
            ValidBitString(quotient@), ValidBitString(remainder@),
            Str2Int(dividend@.subrange(0, i as int)) == Str2Int(quotient@) * Str2Int(divisor@) + Str2Int(remainder@),
            Str2Int(remainder@) < Str2Int(divisor@)
        decreases dividend.len() - i
    {
        remainder.push(dividend[i]);
        
        if Str2Int(remainder@) >= Str2Int(divisor@) {
            let rem_int = Str2Int(remainder@);
            let div_int = Str2Int(divisor@);
            let q = rem_int / div_int;
            let rem_new = rem_int % div_int;
            
            quotient.push('1');
            
            let rem_seq = decimal_to_bitstring(rem_new);
            remainder.clear();
            let mut j: usize = 0;
            while j < rem_seq.len() as usize
                invariant
                    ValidBitString(remainder@),
                    remainder@ == rem_seq.subrange(0, j as int),
                    Str2Int(remainder@) == Str2Int(rem_seq.subrange(0, j as int))
                decreases rem_seq.len() as usize - j
            {
                remainder.push(seq_at_index(rem_seq, j));
                j += 1;
            }
        } else {
            quotient.push('0');
        }
        
        i += 1;
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

