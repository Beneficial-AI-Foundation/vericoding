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
proof fn lemma_str2int_bounds(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s) < pow2(s.len() as nat)
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_str2int_bounds(s.subrange(0, s.len() as int - 1));
        assert(Str2Int(s.subrange(0, s.len() as int - 1)) < pow2((s.len() - 1) as nat));
        assert(pow2((s.len() - 1) as nat) * 2 == pow2(s.len() as nat));
    }
}

proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s.push('0')) == 2 * Str2Int(s)
{
    assert(s.push('0').subrange(0, s.push('0').len() as int - 1) == s);
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
    assert(s.push('1').subrange(0, s.push('1').len() as int - 1) == s);
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2(n - 1) }
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
    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();
    let divisor_val = Str2Int(divisor@);
    
    let mut i: usize = 0;
    while i < dividend.len()
        invariant
            i <= dividend.len(),
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            Str2Int(remainder@) < divisor_val,
            Str2Int(quotient@) * divisor_val + Str2Int(remainder@) == Str2Int(dividend@.subrange(0, i as int))
    {
        let bit = dividend[i];
        
        proof {
            if remainder@.len() == 0 {
                assert(Str2Int(remainder@) == 0);
            } else {
                lemma_str2int_bounds(remainder@);
            }
            if bit == '0' {
                lemma_str2int_append_zero(remainder@);
            } else {
                lemma_str2int_append_one(remainder@);
            }
        }
        
        remainder.push(bit);
        
        let mut current_val = 0nat;
        let mut j: usize = 0;
        while j < remainder.len()
            invariant
                j <= remainder.len(),
                current_val == Str2Int(remainder@.subrange(0, j as int))
        {
            current_val = current_val * 2 + if remainder[j] == '1' { 1nat } else { 0nat };
            j = j + 1;
        }
        
        if current_val >= divisor_val {
            quotient.push('1');
            
            let mut new_remainder = Vec::<char>::new();
            let diff = (current_val - divisor_val) as nat;
            
            if diff == 0 {
                remainder = new_remainder;
            } else {
                let mut temp = diff;
                let mut bits = Vec::<char>::new();
                while temp > 0
                    invariant
                        temp <= diff
                {
                    if temp % 2 == 1 {
                        bits.push('1');
                    } else {
                        bits.push('0');
                    }
                    temp = temp / 2;
                }
                
                let mut k: usize = bits.len();
                while k > 0
                    invariant
                        k <= bits.len(),
                        ValidBitString(new_remainder@)
                {
                    k = k - 1;
                    new_remainder.push(bits[k]);
                }
                remainder = new_remainder;
            }
            
            proof {
                lemma_str2int_append_one(quotient@.subrange(0, quotient@.len() as int - 1));
            }
        } else {
            quotient.push('0');
            proof {
                lemma_str2int_append_zero(quotient@.subrange(0, quotient@.len() as int - 1));
            }
        }
        
        i = i + 1;
    }
    
    if quotient.len() == 0 {
        quotient.push('0');
    }
    
    if remainder.len() == 0 {
        remainder.push('0');
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

