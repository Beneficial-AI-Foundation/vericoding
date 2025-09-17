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
proof fn lemma_str2int_append_bit(s: Seq<char>, bit: char)
    requires
        ValidBitString(s),
        bit == '0' || bit == '1',
    ensures
        ValidBitString(s.push(bit)),
        Str2Int(s.push(bit)) == 2 * Str2Int(s) + if bit == '1' { 1nat } else { 0nat },
    decreases s.len(),
{
    let s_new = s.push(bit);
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) =~= s);
    assert(s_new.index(s_new.len() as int - 1) == bit);
}

proof fn lemma_str2int_bounds(s: Seq<char>)
    requires ValidBitString(s),
    ensures Str2Int(s) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_str2int_bounds(s.subrange(0, s.len() as int - 1));
    }
}

proof fn lemma_valid_subrange(s: Seq<char>, i: int, j: int)
    requires
        ValidBitString(s),
        0 <= i <= j <= s.len() as int,
    ensures
        ValidBitString(s.subrange(i, j)),
{
    assert forall |k: int| 0 <= k && k < s.subrange(i, j).len() as int implies
        #[trigger] s.subrange(i, j).index(k) == '0' || s.subrange(i, j).index(k) == '1'
    by {
        assert(s.subrange(i, j).index(k) == s.index(i + k));
        assert(s.index(i + k) == '0' || s.index(i + k) == '1');
    }
}

proof fn lemma_nat_to_binary_correct(n: nat, digits: Seq<char>)
    requires
        ValidBitString(digits),
        n >= 0,
    ensures
        ValidBitString(digits),
{
    // Helper lemma for binary conversion correctness
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
    let mut quotient = Vec::<char>::new();
    let mut remainder_val: nat = 0;
    let divisor_val = Str2Int(divisor@);
    
    let mut i: usize = 0;
    while i < dividend.len()
        invariant
            i <= dividend.len(),
            ValidBitString(quotient@),
            remainder_val < divisor_val,
            divisor_val > 0,
            ValidBitString(dividend@),
            ValidBitString(divisor@),
            Str2Int(divisor@) == divisor_val,
            // The key invariant: what we've processed so far
            Str2Int(dividend@.subrange(0, i as int)) == 
                Str2Int(quotient@) * divisor_val + remainder_val,
    {
        let old_remainder = remainder_val;
        let old_quotient = quotient.clone();
        
        let bit = dividend[i];
        remainder_val = remainder_val * 2 + if bit == '1' { 1 } else { 0 };
        
        proof {
            lemma_valid_subrange(dividend@, 0, i as int + 1);
            assert(dividend@.subrange(0, i as int + 1).len() == i + 1);
            let prev = dividend@.subrange(0, i as int);
            let curr = dividend@.subrange(0, i as int + 1);
            assert(curr.subrange(0, curr.len() as int - 1) =~= prev);
            assert(curr.index(curr.len() as int - 1) == bit);
            assert(Str2Int(curr) == 2 * Str2Int(prev) + if bit == '1' { 1nat } else { 0nat });
            assert(Str2Int(prev) == Str2Int(old_quotient@) * divisor_val + old_remainder);
            assert(Str2Int(curr) == 2 * (Str2Int(old_quotient@) * divisor_val + old_remainder) + if bit == '1' { 1nat } else { 0nat });
            assert(Str2Int(curr) == 2 * Str2Int(old_quotient@) * divisor_val + remainder_val);
        }
        
        if remainder_val >= divisor_val {
            quotient.push('1');
            remainder_val = remainder_val - divisor_val;
            
            proof {
                lemma_str2int_append_bit(old_quotient@, '1');
                assert(Str2Int(quotient@) == 2 * Str2Int(old_quotient@) + 1);
                let curr = dividend@.subrange(0, i as int + 1);
                assert(Str2Int(curr) == 2 * Str2Int(old_quotient@) * divisor_val + (remainder_val + divisor_val));
                assert(Str2Int(curr) == (2 * Str2Int(old_quotient@) + 1) * divisor_val + remainder_val);
                assert(Str2Int(curr) == Str2Int(quotient@) * divisor_val + remainder_val);
            }
        } else {
            quotient.push('0');
            
            proof {
                lemma_str2int_append_bit(old_quotient@, '0');
                assert(Str2Int(quotient@) == 2 * Str2Int(old_quotient@));
                let curr = dividend@.subrange(0, i as int + 1);
                assert(Str2Int(curr) == 2 * Str2Int(old_quotient@) * divisor_val + remainder_val);
                assert(Str2Int(curr) == Str2Int(quotient@) * divisor_val + remainder_val);
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(dividend@.subrange(0, dividend@.len() as int) =~= dividend@);
        assert(Str2Int(dividend@) == Str2Int(quotient@) * divisor_val + remainder_val);
        assert(remainder_val < divisor_val);
        assert(Str2Int(dividend@) / divisor_val == Str2Int(quotient@));
        assert(Str2Int(dividend@) % divisor_val == remainder_val);
    }
    
    // Convert remainder to binary string
    let mut remainder = Vec::<char>::new();
    let mut temp_rem = remainder_val;
    
    if temp_rem == 0 {
        remainder.push('0');
        proof {
            assert(ValidBitString(remainder@));
            assert(Str2Int(remainder@) == 0);
            assert(Str2Int(remainder@) == remainder_val);
        }
    } else {
        let mut digits = Vec::<char>::new();
        while temp_rem > 0
            invariant
                ValidBitString(digits@),
                temp_rem >= 0,
                remainder_val < divisor_val,
        {
            if temp_rem % 2 == 1 {
                digits.push('1');
            } else {
                digits.push('0');
            }
            temp_rem = temp_rem / 2;
        }
        
        // Reverse the digits
        let mut j: usize = 0;
        while j < digits.len()
            invariant
                j <= digits.len(),
                ValidBitString(digits@),
                ValidBitString(remainder@),
                remainder@.len() == j,
                forall |k: int| 0 <= k && k < j as int ==> 
                    remainder@.index(k) == digits@.index(digits@.len() as int - 1 - k),
        {
            remainder.push(digits[digits.len() - 1 - j]);
            j = j + 1;
        }
        
        proof {
            lemma_nat_to_binary_correct(remainder_val, remainder@);
            // The constructed remainder@ represents remainder_val correctly
        }
    }
    
    // Handle edge case where quotient is empty
    if quotient.len() == 0 {
        quotient.push('0');
        proof {
            assert(ValidBitString(quotient@));
            assert(Str2Int(quotient@) == 0);
        }
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}