
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
/* helper modified by LLM (iteration 5): simplified helper functions and added bounds checking */
exec fn char_to_digit(c: char) -> (result: u8)
    requires c == '0' || c == '1'
    ensures result == 0 || result == 1,
            (c == '0') ==> (result == 0),
            (c == '1') ==> (result == 1)
{
    if c == '1' { 1 } else { 0 }
}

exec fn digit_to_char(d: u8) -> (result: char)
    requires d == 0 || d == 1
    ensures result == '0' || result == '1',
            (d == 0) ==> (result == '0'),
            (d == 1) ==> (result == '1')
{
    if d == 1 { '1' } else { '0' }
}

proof fn valid_char_at_index(s: &[char], i: usize)
    requires ValidBitString(s@), i < s.len()
    ensures s[i] == '0' || s[i] == '1'
{
    assert(s@.index(i as int) == '0' || s@.index(i as int) == '1');
}
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_Add_DivMod_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed precondition violations and termination */
{
    let mut result = Vec::<char>::new();
    let mut carry: u8 = 0;
    let mut i = 0;
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    
    while i < max_len || carry > 0
        invariant
            i <= max_len,
            carry == 0 || carry == 1,
            ValidBitString(result@)
        decreases 2 * max_len + 2 - 2 * i - carry as usize
    {
        let bit_a = if i < a.len() {
            proof {
                valid_char_at_index(a, a.len() - 1 - i);
            }
            char_to_digit(a[a.len() - 1 - i])
        } else {
            0
        };
        
        let bit_b = if i < b.len() {
            proof {
                valid_char_at_index(b, b.len() - 1 - i);
            }
            char_to_digit(b[b.len() - 1 - i])
        } else {
            0
        };
        
        let sum = bit_a + bit_b + carry;
        let result_bit = sum % 2;
        carry = sum / 2;
        
        result.push(digit_to_char(result_bit));
        i += 1;
    }
    
    // Reverse the result since we built it backwards
    let mut final_result = Vec::<char>::new();
    let mut j = result.len();
    
    while j > 0
        invariant
            j <= result.len(),
            ValidBitString(final_result@),
            ValidBitString(result@)
        decreases j
    {
        j -= 1;
        final_result.push(result[j]);
    }
    
    if final_result.len() == 0 {
        final_result.push('0');
    }
    
    final_result
}
// </vc-code>

fn main() {}
}

