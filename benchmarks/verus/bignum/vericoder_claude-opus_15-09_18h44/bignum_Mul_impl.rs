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
/* helper modified by LLM (iteration 10): fixed decreases clause type error */
exec fn add_binary(s1: &[char], s2: &[char]) -> (result: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
    ensures
        ValidBitString(result@),
        Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@),
{
    let mut result = Vec::<char>::new();
    let mut carry: u8 = 0;
    let mut i: usize = 0;
    
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len || carry > 0
        invariant
            0 <= i,
            i <= max_len + 1,
            carry <= 1,
            ValidBitString(result@),
            i <= usize::MAX - 1,
        decreases
            if i < max_len { (max_len - i) as int + (carry as int) } else { carry as int }
    {
        let mut sum: u8 = carry;
        
        if i < s1.len() {
            let idx = s1.len() - 1 - i;
            if s1[idx] == '1' {
                sum = sum + 1;
            }
        }
        
        if i < s2.len() {
            let idx = s2.len() - 1 - i;
            if s2[idx] == '1' {
                sum = sum + 1;
            }
        }
        
        if sum % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        
        carry = sum / 2;
        
        if i >= max_len && carry == 0 {
            proof {
                assert(i >= max_len);
                assert(carry == 0);
            }
            break;
        }
        
        i = i + 1;
    }
    
    let mut reversed = Vec::<char>::new();
    let mut j: usize = result.len();
    while j > 0
        invariant
            0 <= j,
            j <= result.len(),
            ValidBitString(result@),
            ValidBitString(reversed@),
            reversed.len() == result.len() - j,
        decreases j
    {
        j = j - 1;
        reversed.push(result[j]);
    }
    
    if reversed.len() == 0 {
        reversed.push('0');
    }
    
    reversed
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): implement actual multiplication logic without assume */
    if s2.len() == 0 || (s2.len() == 1 && s2[0] == '0') {
        let mut result = Vec::<char>::new();
        result.push('0');
        proof {
            assert(ValidBitString(result@));
            assert(result@.len() == 1);
            assert(result@[0] == '0');
        }
        return result;
    }
    
    if s1.len() == 0 || (s1.len() == 1 && s1[0] == '0') {
        let mut result = Vec::<char>::new();
        result.push('0');
        proof {
            assert(ValidBitString(result@));
            assert(result@.len() == 1);
            assert(result@[0] == '0');
        }
        return result;
    }
    
    let mut result = Vec::<char>::new();
    result.push('0');
    
    let mut shifted_s1 = Vec::<char>::new();
    let mut k: usize = 0;
    while k < s1.len()
        invariant
            0 <= k,
            k <= s1.len(),
            shifted_s1.len() == k,
            ValidBitString(s1@),
            ValidBitString(shifted_s1@),
        decreases s1.len() - k
    {
        shifted_s1.push(s1[k]);
        k = k + 1;
    }
    
    let mut i: usize = s2.len();
    
    while i > 0
        invariant
            0 <= i,
            i <= s2.len(),
            ValidBitString(result@),
            ValidBitString(shifted_s1@),
        decreases i
    {
        i = i - 1;
        
        if s2[i] == '1' {
            result = add_binary(&result, &shifted_s1);
        }
        
        if i > 0 {
            shifted_s1.push('0');
        }
    }
    
    proof {
        assert(ValidBitString(result@));
    }
    
    result
}
// </vc-code>

fn main() {}
}


