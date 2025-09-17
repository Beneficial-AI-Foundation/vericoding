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
/* helper modified by LLM (iteration 4): fixed type error by using nat subtraction with explicit bounds check */
spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn lemma_str2int_pow2(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < pow2(s.len() as nat)
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_str2int_pow2(s.subrange(0, s.len() as int - 1));
    }
}

fn char_to_digit_valid(c: char) -> (result: u8)
    requires c == '0' || c == '1'
    ensures result == 0 || result == 1
{
    if c == '0' { 0u8 } else { 1u8 }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed borrowing error by using separate variable to store value before mutation */
    let mut result = Vec::<char>::new();
    
    if a.len() == 0 && b.len() == 0 {
        result.push('0');
        return result;
    }
    
    let mut carry = 0u8;
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    
    let mut i = 0;
    while i < max_len
        invariant
            i <= max_len,
            ValidBitString(result@),
            carry <= 1,
            max_len == if a.len() > b.len() { a.len() } else { b.len() },
        decreases max_len - i
    {
        let a_bit = if i < a.len() && a[a.len() - 1 - i] == '1' { 1u8 } else { 0u8 };
        let b_bit = if i < b.len() && b[b.len() - 1 - i] == '1' { 1u8 } else { 0u8 };
        
        let sum = a_bit + b_bit + carry;
        let result_bit = sum % 2;
        carry = sum / 2;
        
        if result_bit == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        
        i += 1;
    }
    
    if carry == 1 {
        result.push('1');
    }
    
    let mut j = 0;
    while j < result.len() / 2
        invariant
            j <= result.len() / 2,
            ValidBitString(result@),
        decreases result.len() / 2 - j
    {
        let temp = result[j];
        let other_value = result[result.len() - 1 - j];
        result.set(j, other_value);
        result.set(result.len() - 1 - j, temp);
        j += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}

