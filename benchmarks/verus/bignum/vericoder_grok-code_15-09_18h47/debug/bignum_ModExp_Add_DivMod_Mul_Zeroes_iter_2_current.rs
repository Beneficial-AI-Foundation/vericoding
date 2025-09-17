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
/* helper modified by LLM (iteration 2): Cast integer literals to int type */
fn get_bit(s: &[char], index: usize) -> int { if index < s.len() { if s[index] == '1' { 1int } else { 0int } } else { 0int } }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Cast literals to int type and fix type mismatches in variables and loop conditions */
{
    let a_len_int = a.len() as int;
    let b_len_int = b.len() as int;
    let max_len_int = if a_len_int > b_len_int { a_len_int } else { b_len_int };
    let mut carry = 0int;
    let mut result: Vec<char> = Vec::new();
    let mut i = 0int;
    while i < max_len_int
        invariant
            0 <= i <= max_len_int,
            0 <= carry <= 1int,
            result@.len() == i,
            forall |k: int| 0 <= k && k < result@.len() ==> (result@[k] == '0' || result@[k] == '1')
    {
        let bit_a = get_bit(a, i as usize);
        let bit_b = get_bit(b, i as usize);
        let sum = bit_a + bit_b + carry;
        let new_bit = if sum % 2int == 1int { '1' } else { '0' };
        carry = sum / 2int;
        result.push(new_bit);
        i += 1int;
    }
    if carry > 0int {
        result.push('1');
    }
    if result.len() == 0 {
        result.push('0');
    }
    result.reverse();
    result
}
// </vc-code>

fn main() {}
}

