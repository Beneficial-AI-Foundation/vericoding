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
// Helper lemma to show that padding with leading zeros doesn't change the integer value
proof fn lemma_leading_zeros_preserve_value(s: Seq<char>, zeros: nat)
    requires ValidBitString(s),
    ensures Str2Int(seq![|i: int| if i < zeros { '0' } else { s[i - zeros] }; zeros + s.len()]) == Str2Int(s),
    decreases zeros,
{
    if zeros == 0 {
        assert(seq![|i: int| if i < 0 { '0' } else { s[i] }; s.len()] =~= s);
    } else {
        let padded = seq![|i: int| if i < zeros { '0' } else { s[i - zeros] }; zeros + s.len()];
        assert(padded.len() > 0);
        assert(padded[padded.len() - 1] == s[s.len() - 1]);
        let padded_prefix = padded.subrange(0, padded.len() - 1);
        let s_prefix = s.subrange(0, s.len() - 1);
        lemma_leading_zeros_preserve_value(s_prefix, zeros);
    }
}

// Helper function to ensure two bit strings have the same length by padding with '0's
exec fn pad_to_same_length(a: &[char], b: &[char]) -> (res: (Vec<char>, Vec<char>))
    requires ValidBitString(a@), ValidBitString(b@),
    ensures ValidBitString(res.0@), ValidBitString(res.1@),
            res.0@.len() == res.1@.len(),
            res.0@.len() >= a@.len(),
            res.1@.len() >= b@.len(),
            Str2Int(res.0@) == Str2Int(a@),
            Str2Int(res.1@) == Str2Int(b@),
{
    let mut a_vec = Vec::new();
    let mut b_vec = Vec::new();
    
    let a_len = a.len();
    let b_len = b.len();
    
    if a_len >= b_len {
        // Copy a as is
        let mut i: usize = 0;
        while i < a_len
            invariant
                0 <= i <= a_len,
                a_len == a@.len(),
                a_vec@.len() == i as int,
                forall |j: int| 0 <= j && j < i ==> a_vec@[j] == a@[j],
                ValidBitString(a@),
                ValidBitString(a_vec@),
                a_vec@ =~= a@.subrange(0, i as int),
            decreases a_len - i,
        {
            a_vec.push(a[i]);
            i += 1;
        }
        assert(a_vec@ =~= a@);
        
        // Pad b with leading zeros
        let padding = a_len - b_len;
        let mut i: usize = 0;
        while i < padding
            invariant
                0 <= i <= padding,
                padding == a_len - b_len,
                b_vec@.len() == i as int,
                forall |j: int| 0 <= j && j < i ==> b_vec@[j] == '0',
                ValidBitString(b_vec@),
            decreases padding - i,
        {
            b_vec.push('0');
            i += 1;
        }
        
        let mut i: usize = 0;
        while i < b_len
            invariant
                0 <= i <= b_len,
                b_len == b@.len(),
                padding == a_len - b_len,
                b_vec@.len() == (padding + i) as int,
                forall |j: int| 0 <= j && j < padding ==> b_vec@[j] == '0',
                forall |j: int| 0 <= j && j < i ==> b_vec@[(padding + j) as int] == b@[j],
                ValidBitString(b@),
                ValidBitString(b_vec@),
            decreases b_len - i,
        {
            b_vec.push(b[i]);
            i += 1;
        }
        
        proof {
            lemma_leading_zeros_preserve_value(b@, padding as nat);
            assert(b_vec@ =~= seq![|j: int| if j < padding { '0' } else { b@[j - padding] }; padding + b@.len()]);
        }
    } else {
        // Pad a with leading zeros
        let padding = b_len - a_len;
        let mut i: usize = 0;
        while i < padding
            invariant
                0 <= i <= padding,
                padding == b_len - a_len,
                a_vec@.len() == i as int,
                forall |j: int| 0 <= j && j < i ==> a_vec@[j] == '0',
                ValidBitString(a_vec@),
            decreases padding - i,
        {
            a_vec.push('0');
            i += 1;
        }
        
        let mut i: usize = 0;
        while i < a_len
            invariant
                0 <= i <= a_len,
                a_len == a@.len(),
                padding == b_len - a_len,
                a_vec@.len() == (padding + i) as int,
                forall |j: int| 0 <= j && j < padding ==> a_vec@[j] == '0',
                forall |j: int| 0 <= j && j < i ==> a_vec@[(padding + j) as int] == a@[j],
                ValidBitString(a@),
                ValidBitString(a_vec@),
            decreases a_len - i,
        {
            a_vec.push(a[i]);
            i += 1;
        }
        
        proof {
            lemma_leading_zeros_preserve_value(a@, padding as nat);
            assert(a_vec@ =~= seq![|j: int| if j < padding { '0' } else { a@[j - padding] }; padding + a@.len()]);
        }
        
        // Copy b as is
        let mut i: usize = 0;
        while i < b_len
            invariant
                0 <= i <= b_len,
                b_len == b@.len(),
                b_vec@.len() == i as int,
                forall |j: int| 0 <= j && j < i ==> b_vec@[j] == b@[j],
                ValidBitString(b@),
                ValidBitString(b_vec@),
                b_vec@ =~= b@.subrange(0, i as int),
            decreases b_len - i,
        {
            b_vec.push(b[i]);
            i += 1;
        }
        assert(b_vec@ =~= b@);
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
        assert(ValidBitString(result@));
        return result;
    }
    
    let (a_padded, b_padded) = pad_to_same_length(a, b);
    let len = a_padded.len();
    assert(a_padded@.len() == b_padded@.len());
    
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < len
        invariant
            0 <= i <= len,
            len == a_padded@.len(),
            len == b_padded@.len(),
            result@.len() == i as int,
            ValidBitString(a_padded@),
            ValidBitString(b_padded@),
            ValidBitString(result@),
            forall |j: int| 0 <= j && j < i ==> 
                (result@[j] == '0' || result@[j] == '1'),
        decreases len - i,
    {
        assert(0 <= i && i < a_padded@.len());
        assert(0 <= i && i < b_padded@.len());
        let bit_a = a_padded[i];
        let bit_b = b_padded[i];
        
        assert(bit_a == '0' || bit_a == '1');
        assert(bit_b == '0' || bit_b == '1');
        
        // XOR operation (addition mod 2)
        if bit_a == bit_b {
            result.push('0');
        } else {
            result.push('1');
        }
        
        assert(forall |j: int| 0 <= j && j <= i ==> (result@[j] == '0' || result@[j] == '1'));
        i += 1;
    }
    
    // Remove leading zeros if any (keep at least one digit)
    let mut start: usize = 0;
    while start < result.len() - 1
        invariant
            0 <= start < result.len(),
            ValidBitString(result@),
        decreases result.len() - 1 - start,
    {
        if result[start] != '0' {
            break;
        }
        start += 1;
    }
    
    let mut final_result = Vec::new();
    let mut i = start;
    while i < result.len()
        invariant
            start <= i <= result.len(),
            final_result@.len() == (i - start) as int,
            ValidBitString(result@),
            forall |j: int| 0 <= j && j < i - start ==>
                final_result@[j] == result@[(start + j) as int],
            forall |j: int| 0 <= j && j < i - start ==>
                (final_result@[j] == '0' || final_result@[j] == '1'),
            ValidBitString(final_result@),
        decreases result.len() - i,
    {
        assert(0 <= i && i < result@.len());
        assert(result@[i as int] == '0' || result@[i as int] == '1');
        final_result.push(result[i]);
        i += 1;
    }
    
    assert(ValidBitString(final_result@));
    final_result
}
// </vc-code>

fn main() {}
}