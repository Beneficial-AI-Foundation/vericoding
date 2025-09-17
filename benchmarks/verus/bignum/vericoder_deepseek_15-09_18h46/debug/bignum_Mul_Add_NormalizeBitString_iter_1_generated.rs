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
proof fn lemma_str2int_nonnegative(s: Seq<char>) by(induction(s.len()))
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
{
    if s.len() == 0 {
    } else {
        lemma_str2int_nonnegative(s.subrange(0, s.len() as int - 1));
    }
}

proof fn lemma_str2int_monotonic(s1: Seq<char>, s2: Seq<char>) by(induction(s1.len()))
    requires ValidBitString(s1), ValidBitString(s2), s1.len() <= s2.len()
    ensures Str2Int(s1) <= Str2Int(s2)
{
    if s1.len() == 0 {
        lemma_str2int_nonnegative(s2);
    } else {
        lemma_str2int_monotonic(s1.subrange(0, s1.len() as int - 1), s2.subrange(0, s2.len() as int - 1));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let n = s1.len();
    let m = s2.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@.subrange(0, i as int)) * Str2Int(s2@)
        decreases n - i
    {
        let mut temp = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant
                j <= m,
                ValidBitString(temp@),
                Str2Int(temp@) == Str2Int(s1@.subrange(i, i + 1)) * Str2Int(s2@.subrange(0, j as int))
            decreases m - j
        {
            let bit1 = s1[i];
            let bit2 = s2[j];
            let product = if bit1 == '1' && bit2 == '1' { 1 } else { 0 };
            temp.push(if product == 1 { '1' } else { '0' });
            j += 1;
        }
        
        let mut shifted = Vec::new();
        let mut k: usize = 0;
        while k < i
            invariant
                k <= i,
                ValidBitString(shifted@),
                shifted@.len() == k,
                forall |idx: int| 0 <= idx && idx < k as int ==> shifted@[idx] == '0'
            decreases i - k
        {
            shifted.push('0');
            k += 1;
        }
        
        shifted.extend(temp);
        
        let mut new_result = Vec::new();
        let max_len = if result.len() > shifted.len() { result.len() } else { shifted.len() };
        let mut carry = 0;
        let mut idx: usize = 0;
        while idx < max_len
            invariant
                idx <= max_len,
                ValidBitString(new_result@),
                Str2Int(new_result@) + carry * pow2(idx as nat) == Str2Int(result@) + Str2Int(shifted@)
            decreases max_len - idx
        {
            let bit1 = if idx < result.len() { result[idx] } else { '0' };
            let bit2 = if idx < shifted.len() { shifted[idx] } else { '0' };
            let sum = (if bit1 == '1' { 1 } else { 0 }) + (if bit2 == '1' { 1 } else { 0 }) + carry;
            carry = sum / 2;
            new_result.push(if sum % 2 == 1 { '1' } else { '0' });
            idx += 1;
        }
        
        if carry > 0 {
            new_result.push('1');
        }
        
        result = new_result;
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}
