
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
/* helper modified by LLM (iteration 4): added decreases clause to pow2 function */
spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

spec fn add_bit_strings(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
{
    if s1.len() == 0 && s2.len() == 0 {
        seq!['0']
    } else {
        add_with_carry(s1, s2, false, 0)
    }
}

spec fn add_with_carry(s1: Seq<char>, s2: Seq<char>, carry: bool, pos: nat) -> Seq<char>
    decreases if s1.len() > s2.len() { s1.len() } else { s2.len() } - pos
{
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    if pos >= max_len && !carry {
        seq![]
    } else {
        let bit1 = if pos < s1.len() { s1.index(s1.len() as int - 1 - pos as int) == '1' } else { false };
        let bit2 = if pos < s2.len() { s2.index(s2.len() as int - 1 - pos as int) == '1' } else { false };
        let sum = (if bit1 { 1nat } else { 0nat }) + (if bit2 { 1nat } else { 0nat }) + (if carry { 1nat } else { 0nat });
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        let new_carry = sum >= 2;
        add_with_carry(s1, s2, new_carry, pos + 1).push(result_bit)
    }
}

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
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_Add_DivMod_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): added decreases clause to loops */
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
        decreases max_len + 1 - i + carry as usize
    {
        let bit_a = if i < a.len() {
            char_to_digit(a[a.len() - 1 - i])
        } else {
            0
        };
        
        let bit_b = if i < b.len() {
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

