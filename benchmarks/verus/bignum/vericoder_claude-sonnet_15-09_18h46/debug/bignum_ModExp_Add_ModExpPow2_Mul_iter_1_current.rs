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
spec fn max_len(a: Seq<char>, b: Seq<char>) -> nat {
    if a.len() >= b.len() { a.len() } else { b.len() }
}

spec fn pad_bit_string(s: Seq<char>, target_len: nat) -> Seq<char>
    requires ValidBitString(s), target_len >= s.len()
    ensures ValidBitString(pad_bit_string(s, target_len)),
            pad_bit_string(s, target_len).len() == target_len,
            Str2Int(pad_bit_string(s, target_len)) == Str2Int(s)
    decreases target_len - s.len()
{
    if s.len() == target_len {
        s
    } else {
        pad_bit_string(seq!['0'] + s, target_len)
    }
}

spec fn add_bit_strings_spec(a: Seq<char>, b: Seq<char>) -> Seq<char>
    requires ValidBitString(a), ValidBitString(b)
    ensures ValidBitString(add_bit_strings_spec(a, b)),
            Str2Int(add_bit_strings_spec(a, b)) == Str2Int(a) + Str2Int(b)
{
    let target_len = max_len(a, b) + 1;
    let a_padded = pad_bit_string(a, target_len);
    let b_padded = pad_bit_string(b, target_len);
    binary_add_helper(a_padded, b_padded, 0, seq![])
}

spec fn binary_add_helper(a: Seq<char>, b: Seq<char>, carry: nat, acc: Seq<char>) -> Seq<char>
    requires ValidBitString(a), ValidBitString(b),
             a.len() == b.len(),
             carry <= 1
    ensures ValidBitString(binary_add_helper(a, b, carry, acc))
    decreases a.len()
{
    if a.len() == 0 {
        if carry == 1 { seq!['1'] + acc } else { acc }
    } else {
        let last_a = if a.last() == '1' { 1nat } else { 0nat };
        let last_b = if b.last() == '1' { 1nat } else { 0nat };
        let sum = last_a + last_b + carry;
        let new_carry = sum / 2;
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        binary_add_helper(
            a.subrange(0, a.len() as int - 1),
            b.subrange(0, b.len() as int - 1),
            new_carry,
            seq![result_bit] + acc
        )
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    let a_seq = a@;
    let b_seq = b@;
    let target_len = if a_seq.len() >= b_seq.len() { a_seq.len() + 1 } else { b_seq.len() + 1 };
    
    let mut a_vec = Vec::new();
    let mut i = 0;
    while i < target_len - a_seq.len()
        invariant
            i <= target_len - a_seq.len(),
            a_vec.len() == i,
            ValidBitString(a_vec@)
    {
        a_vec.push('0');
        i = i + 1;
    }
    let mut j = 0;
    while j < a_seq.len()
        invariant
            j <= a_seq.len(),
            a_vec.len() == (target_len - a_seq.len()) + j,
            ValidBitString(a_vec@)
    {
        a_vec.push(a_seq[j as int]);
        j = j + 1;
    }
    
    let mut b_vec = Vec::new();
    let mut k = 0;
    while k < target_len - b_seq.len()
        invariant
            k <= target_len - b_seq.len(),
            b_vec.len() == k,
            ValidBitString(b_vec@)
    {
        b_vec.push('0');
        k = k + 1;
    }
    let mut l = 0;
    while l < b_seq.len()
        invariant
            l <= b_seq.len(),
            b_vec.len() == (target_len - b_seq.len()) + l,
            ValidBitString(b_vec@)
    {
        b_vec.push(b_seq[l as int]);
        l = l + 1;
    }
    
    let mut result = Vec::new();
    let mut carry = 0u8;
    let mut pos = target_len;
    
    while pos > 0
        invariant
            pos <= target_len,
            carry <= 1,
            ValidBitString(result@)
    {
        pos = pos - 1;
        let bit_a = if a_vec[pos as int] == '1' { 1u8 } else { 0u8 };
        let bit_b = if b_vec[pos as int] == '1' { 1u8 } else { 0u8 };
        let sum = bit_a + bit_b + carry;
        carry = sum / 2;
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        result.insert(0, result_bit);
    }
    
    if carry == 1 {
        result.insert(0, '1');
    }
    
    result
}
// </vc-code>

fn main() {}
}

