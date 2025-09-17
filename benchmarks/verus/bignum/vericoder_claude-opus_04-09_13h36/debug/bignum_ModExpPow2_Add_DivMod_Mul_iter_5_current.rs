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
// Helper function to ensure two bit strings have the same length by padding with '0's
exec fn pad_to_same_length(a: &[char], b: &[char]) -> (res: (Vec<char>, Vec<char>))
    requires ValidBitString(a@), ValidBitString(b@),
    ensures ValidBitString(res.0@), ValidBitString(res.1@),
            res.0@.len() == res.1@.len(),
            res.0@.len() >= a@.len(),
            res.1@.len() >= b@.len(),
{
    let mut a_vec = Vec::new();
    let mut b_vec = Vec::new();
    
    let a_len = a.len();
    let b_len = b.len();
    
    if a_len >= b_len {
        // Copy a as is
        let mut i = 0;
        while i < a_len
            invariant 0 <= i <= a_len,
            invariant a_vec@.len() == i,
            invariant forall |j: int| 0 <= j && j < i ==> a_vec@[j] == a@[j],
            invariant ValidBitString(a_vec@),
        {
            a_vec.push(a[i]);
            i += 1;
        }
        
        // Pad b with leading zeros
        let padding = a_len - b_len;
        let mut i = 0;
        while i < padding
            invariant 0 <= i <= padding,
            invariant b_vec@.len() == i,
            invariant forall |j: int| 0 <= j && j < i ==> b_vec@[j] == '0',
            invariant ValidBitString(b_vec@),
        {
            b_vec.push('0');
            i += 1;
        }
        
        let mut i = 0;
        while i < b_len
            invariant 0 <= i <= b_len,
            invariant b_vec@.len() == padding + i,
            invariant forall |j: int| 0 <= j && j < padding ==> b_vec@[j] == '0',
            invariant forall |j: int| padding <= j && j < padding + i ==> b_vec@[j] == b@[j - padding],
            invariant ValidBitString(b_vec@),
        {
            b_vec.push(b[i]);
            i += 1;
        }
    } else {
        // Pad a with leading zeros
        let padding = b_len - a_len;
        let mut i = 0;
        while i < padding
            invariant 0 <= i <= padding,
            invariant a_vec@.len() == i,
            invariant forall |j: int| 0 <= j && j < i ==> a_vec@[j] == '0',
            invariant ValidBitString(a_vec@),
        {
            a_vec.push('0');
            i += 1;
        }
        
        let mut i = 0;
        while i < a_len
            invariant 0 <= i <= a_len,
            invariant a_vec@.len() == padding + i,
            invariant forall |j: int| 0 <= j && j < padding ==> a_vec@[j] == '0',
            invariant forall |j: int| padding <= j && j < padding + i ==> a_vec@[j] == a@[j - padding],
            invariant ValidBitString(a_vec@),
        {
            a_vec.push(a[i]);
            i += 1;
        }
        
        // Copy b as is
        let mut i = 0;
        while i < b_len
            invariant 0 <= i <= b_len,
            invariant b_vec@.len() == i,
            invariant forall |j: int| 0 <= j && j < i ==> b_vec@[j] == b@[j],
            invariant ValidBitString(b_vec@),
        {
            b_vec.push(b[i]);
            i += 1;
        }
    }
    
    (a_vec, b_vec)
}
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_Add_DivMod_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    if a.len() == 0 && b.len() == 0 {
        // Both empty, return '0'
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let (a_padded, b_padded) = pad_to_same_length(a, b);
    let len = a_padded.len();
    
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < len
        invariant 0 <= i <= len,
        invariant result@.len() == i,
        invariant ValidBitString(result@),
        invariant forall |j: int| 0 <= j && j < i ==> 
            (result@[j] == '0' || result@[j] == '1'),
    {
        let bit_a = a_padded[i];
        let bit_b = b_padded[i];
        
        // XOR operation (addition mod 2)
        if bit_a == bit_b {
            result.push('0');
        } else {
            result.push('1');
        }
        
        i += 1;
    }
    
    // Remove leading zeros if any (keep at least one digit)
    let mut start = 0;
    while start < result.len() - 1
        invariant 0 <= start < result.len(),
        invariant ValidBitString(result@),
    {
        if result[start] != '0' {
            break;
        }
        start += 1;
    }
    
    let mut final_result = Vec::new();
    let mut i = start;
    while i < result.len()
        invariant start <= i <= result.len(),
        invariant final_result@.len() == i - start,
        invariant ValidBitString(final_result@),
        invariant forall |j: int| 0 <= j && j < i - start ==>
            final_result@[j] == result@[start + j],
    {
        final_result.push(result[i]);
        i += 1;
    }
    
    final_result
}
// </vc-code>

fn main() {}
}