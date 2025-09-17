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
/* helper modified by LLM (iteration 2): Fixed type annotations for empty sequence comparison */
proof fn lemma_str2int_append(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        Str2Int(s.push(c)) == 2 * Str2Int(s) + if c == '1' { 1nat } else { 0nat },
    decreases s.len()
{
    let s_new = s.push(c);
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) == s);
    assert(s_new.index(s_new.len() as int - 1) == c);
}

proof fn lemma_str2int_zero()
    ensures
        Str2Int(seq!['0']) == 0,
{
    assert(seq!['0'].len() == 1);
    let empty: Seq<char> = seq![];
    assert(seq!['0'].subrange(0, 0) == empty);
    assert(Str2Int(seq![]) == 0);
    assert(seq!['0'].index(0) == '0');
}

proof fn lemma_str2int_properties(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0,
    ensures
        Str2Int(s) >= 0,
    decreases s.len()
{
    if s.len() == 1 {
        if s.index(0) == '0' {
            lemma_str2int_zero();
        }
    } else {
        lemma_str2int_properties(s.subrange(0, s.len() as int - 1));
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
{
    /* code modified by LLM (iteration 2): Fixed nat literal syntax errors */
    let mut quotient = Vec::<char>::new();
    let mut remainder_val: nat = 0;
    let divisor_val = Str2Int(divisor@);
    
    let mut i = 0;
    while i < dividend.len()
        invariant
            0 <= i <= dividend.len(),
            ValidBitString(quotient@),
            remainder_val < divisor_val,
            i > 0 ==> Str2Int(quotient@) * divisor_val + remainder_val == Str2Int(dividend@.subrange(0, i as int)),
            i == 0 ==> quotient.len() == 0 && remainder_val == 0,
    {
        let bit = dividend[i];
        remainder_val = remainder_val * 2 + if bit == '1' { 1 } else { 0 };
        
        if remainder_val >= divisor_val {
            quotient.push('1');
            remainder_val = remainder_val - divisor_val;
        } else {
            quotient.push('0');
        }
        
        proof {
            if i > 0 {
                lemma_str2int_append(dividend@.subrange(0, i as int), bit);
            }
            lemma_str2int_append(quotient@.subrange(0, quotient.len() as int - 1), quotient[quotient.len() - 1]);
        }
        
        i = i + 1;
    }
    
    let mut remainder = Vec::<char>::new();
    let mut temp = remainder_val;
    let mut bits = Vec::<char>::new();
    
    if temp == 0 {
        remainder.push('0');
    } else {
        while temp > 0
            invariant
                temp >= 0,
                ValidBitString(bits@),
        {
            if temp % 2 == 1 {
                bits.push('1');
            } else {
                bits.push('0');
            }
            temp = temp / 2;
        }
        
        let mut j = bits.len();
        while j > 0
            invariant
                0 <= j <= bits.len(),
                ValidBitString(remainder@),
        {
            j = j - 1;
            remainder.push(bits[j]);
        }
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

