
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
/* helper modified by LLM (iteration 2): fixed add_bits signature and ensures clause to resolve compilation error */
exec fn add_bits(b1: char, b2: char, carry_in: char) -> (char, char)
    requires
        b1 == '0' || b1 == '1',
        b2 == '0' || b2 == '1',
        carry_in == '0' || carry_in == '1',
    ensures
        result.0 == '0' || result.0 == '1',
        result.1 == '0' || result.1 == '1',
{
    let i1 = if b1 == '1' { 1 } else { 0 };
    let i2 = if b2 == '1' { 1 } else { 0 };
    let i_carry = if carry_in == '1' { 1 } else { 0 };
    let total = i1 + i2 + i_carry;
    let sum_bit = if total % 2 == 1 { '1' } else { '0' };
    let carry_out_bit = if total >= 2 { '1' } else { '0' };
    (sum_bit, carry_out_bit)
}

proof fn lemma_push_maintains_valid_bit_string(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        ValidBitString(s.push(c)),
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_Add_DivMod_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): no logic change, addressed compilation error in helper */
    let a_len = a.len();
    let b_len = b.len();
    let max_len = if a_len > b_len { a_len } else { b_len };

    let mut result_rev = Vec::<char>::new();
    let mut carry = '0';
    let mut i: int = 0;

    while (i as nat) < max_len
        invariant
            ValidBitString(a@),
            ValidBitString(b@),
            ValidBitString(result_rev@),
            0 <= i && i <= (max_len as int),
            a.len() == a_len,
            b.len() == b_len,
            carry == '0' || carry == '1',
        decreases (max_len as int) - i
    {
        let a_bit = if i < (a_len as int) { a[(a_len as int - 1 - i) as usize] } else { '0' };
        let b_bit = if i < (b_len as int) { b[(b_len as int - 1 - i) as usize] } else { '0' };

        let (sum_bit, next_carry) = add_bits(a_bit, b_bit, carry);

        lemma_push_maintains_valid_bit_string(result_rev@, sum_bit);
        result_rev.push(sum_bit);
        
        carry = next_carry;
        i = i + 1;
    }

    if carry == '1' {
        lemma_push_maintains_valid_bit_string(result_rev@, '1');
        result_rev.push('1');
    }

    let len = result_rev.len();
    let mut result = Vec::<char>::new();
    let mut j: int = 0;
    
    while (j as nat) < len
        invariant
            ValidBitString(result_rev@),
            result_rev.len() == len,
            ValidBitString(result@),
            0 <= j && j <= (len as int),
        decreases (len as int) - j
    {
        let val = result_rev[(len as int - 1 - j) as usize];

        lemma_push_maintains_valid_bit_string(result@, val);
        result.push(val);

        j = j + 1;
    }

    result
}
// </vc-code>

fn main() {}
}

