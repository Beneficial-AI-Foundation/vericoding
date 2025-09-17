
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
/* helper modified by LLM (iteration 2): replaced seq_init with Seq::new and removed unused spec functions */
spec fn char_to_nat(c: char) -> nat {
    if c == '1' { 1nat } else { 0nat }
}

spec fn nat_to_char(n: nat) -> char {
    if n == 1 { '1' } else { '0' }
}

proof fn valid_bit_string_preserved(s: Seq<char>)
    requires ValidBitString(s)
    ensures ValidBitString(s)
{}
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_Add_DivMod_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): simplified implementation without seq_init */
{
    let mut result = Vec::<char>::new();
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    
    let mut carry = 0;
    let mut i = 0;
    
    while i <= max_len
        invariant
            i <= max_len + 1,
            carry == 0 || carry == 1,
            ValidBitString(result@),
        decreases max_len + 1 - i
    {
        let bit_a = if i < a.len() && (a.len() - 1 - i) < a.len() {
            if a[a.len() - 1 - i] == '1' { 1 } else { 0 }
        } else { 0 };
        
        let bit_b = if i < b.len() && (b.len() - 1 - i) < b.len() {
            if b[b.len() - 1 - i] == '1' { 1 } else { 0 }
        } else { 0 };
        
        let sum = bit_a + bit_b + carry;
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;
        
        result.push(result_bit);
        i += 1;
        
        if i > max_len && carry == 0 {
            break;
        }
    }
    
    result.reverse();
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}

