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
/* helper modified by LLM (iteration 3): Changed return type to usize and logic to return u8 (0 or 1) for bit value, removing int usage */
fn get_bit(s: &[char], index: usize) -> usize { if index < s.len() { if s[index] == '1' { 1 } else { 0 } } else { 0 } }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Replaced int variables with usize for lengths and indices, cast to int only in invariant and loop */
{
    let a_len: usize = a.len();
    let b_len: usize = b.len();
    let max_len = if a_len > b_len { a_len } else { b_len };
    let mut carry: usize = 0;
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < max_len
        invariant
            (i as int) <= (max_len as int),
            0 <= carry <= 1,
            result@.len() == (i as int),
            forall |k: int| 0 <= k && k < result@.len() ==> (result@[k] == '0' || result@[k] == '1')
    {
        let bit_a = get_bit(a, i);
        let bit_b = get_bit(b, i);
        let sum = bit_a + bit_b + carry;
        let new_bit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;
        result.push(new_bit);
        i += 1;
    }
    if carry > 0 {
        result.push('1');
    }
    if result.is_empty() {
        result.push('0');
    }
    result.reverse();
    result
}
// </vc-code>

fn main() {}
}

