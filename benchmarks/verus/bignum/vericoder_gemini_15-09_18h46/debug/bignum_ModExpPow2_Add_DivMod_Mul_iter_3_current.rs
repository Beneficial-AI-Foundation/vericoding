
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
/* helper modified by LLM (iteration 3): named return values in add_bits to fix scope error */
exec fn add_bits(b1: char, b2: char, carry_in: char) -> (sum_bit: char, carry_out_bit: char)
    requires
        b1 == '0' || b1 == '1',
        b2 == '0' || b2 == '1',
        carry_in == '0' || carry_in == '1',
    ensures
        sum_bit == '0' || sum_bit == '1',
        carry_out_bit == '0' || carry_out_bit == '1',
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
    /* code modified by LLM (iteration 3): changed loop counters to usize and fixed indexing to resolve ghost code errors */
    let a_len = a.len();
    let b_len = b.len();
    let max_len = if a_len > b_len { a_len } else { b_len };

    let mut result_rev = Vec::<char>::new();
    let mut carry = '0';
    let mut i: usize = 0;

    while i < max_len
        invariant
            ValidBitString(a@),
            ValidBitString(b@),
            ValidBitString(result_rev@),
            i <= max_len,
            a.len() == a_len,
            b.len() == b_len,
            carry == '0' || carry == '1',
        decreases max_len - i
    {
        let a_bit = if i < a_len { a[a_len - 1 - i] } else { '0' };
        let b_bit = if i < b_len { b[b_len - 1 - i] } else { '0' };

        let (sum_bit, next_carry) = add_bits(a_bit, b_bit, carry);

        proof {
            lemma_push_maintains_valid_bit_string(result_rev@, sum_bit);
        }
        result_rev.push(sum_bit);
        
        carry = next_carry;
        i = i + 1;
    }

    if carry == '1' {
        proof {
            lemma_push_maintains_valid_bit_string(result_rev@, '1');
        }
        result_rev.push('1');
    }

    let len = result_rev.len();
    let mut result = Vec::<char>::new();
    let mut j: usize = 0;
    
    while j < len
        invariant
            ValidBitString(result_rev@),
            result_rev.len() == len,
            ValidBitString(result@),
            j <= len,
        decreases len - j
    {
        let val = result_rev[len - 1 - j];
        proof {
            lemma_push_maintains_valid_bit_string(result@, val);
        }
        result.push(val);

        j = j + 1;
    }

    result
}
// </vc-code>

fn main() {}
}

