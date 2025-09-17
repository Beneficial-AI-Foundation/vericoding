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
proof fn lemma_valid_bit_string_push(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c))
{
    assert forall |i: int| 0 <= i && i < s.push(c).len() implies 
        (s.push(c).index(i) == '0' || s.push(c).index(i) == '1') by {
        let pushed = s.push(c);
        if i < s.len() {
            assert(pushed.index(i) == s.index(i));
        } else {
            assert(i == s.len());
            assert(pushed.index(i) == c);
        }
    }
}

proof fn lemma_valid_bit_string_empty()
    ensures ValidBitString(Seq::<char>::empty())
{
    assert forall |i: int| 0 <= i && i < 0 implies false by {};
}

exec fn char_to_digit(c: char) -> (res: u8)
    requires c == '0' || c == '1'
    ensures res == 0 || res == 1
    ensures (c == '0') ==> (res == 0)
    ensures (c == '1') ==> (res == 1)
{
    if c == '0' { 0 } else { 1 }
}

exec fn digit_to_char(d: u8) -> (res: char)
    requires d == 0 || d == 1
    ensures res == '0' || res == '1'
    ensures (d == 0) ==> (res == '0')
    ensures (d == 1) ==> (res == '1')
{
    if d == 0 { '0' } else { '1' }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<char>::new();
    
    proof {
        lemma_valid_bit_string_empty();
    }
    
    let len_a = a.len();
    let len_b = b.len();
    let max_len = if len_a > len_b { len_a } else { len_b };
    
    let mut carry = 0u8;
    let mut i = 0;
    
    while i < max_len || carry > 0
        invariant 
            i <= max_len,
            carry == 0 || carry == 1,
            ValidBitString(result@),
    {
        let mut sum = carry;
        
        if i < len_a && len_a > 0 {
            let digit_a = char_to_digit(a[len_a - 1 - i]);
            sum = sum + digit_a;
        }
        
        if i < len_b && len_b > 0 {
            let digit_b = char_to_digit(b[len_b - 1 - i]);
            sum = sum + digit_b;
        }
        
        let result_digit = sum % 2;
        carry = sum / 2;
        
        let result_char = digit_to_char(result_digit);
        result.push(result_char);
        
        proof {
            lemma_valid_bit_string_push(old(result)@, result_char);
        }
        
        i = i + 1;
    }
    
    // Reverse the result since we built it backwards
    let mut final_result = Vec::<char>::new();
    proof {
        lemma_valid_bit_string_empty();
    }
    
    let mut j = 0;
    while j < result.len()
        invariant
            j <= result.len(),
            ValidBitString(result@),
            ValidBitString(final_result@),
    {
        let idx = result.len() - 1 - j;
        let ch = result[idx];
        final_result.push(ch);
        
        proof {
            lemma_valid_bit_string_push(old(final_result)@, ch);
        }
        
        j = j + 1;
    }
    
    // Handle empty result case
    if final_result.len() == 0 {
        final_result.push('0');
        proof {
            lemma_valid_bit_string_push(old(final_result)@, '0');
        }
    }
    
    final_result
}
// </vc-code>

fn main() {}
}