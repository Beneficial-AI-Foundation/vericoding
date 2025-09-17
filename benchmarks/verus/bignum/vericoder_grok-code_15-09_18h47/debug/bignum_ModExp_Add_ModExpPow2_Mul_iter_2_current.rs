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
/* helper modified by LLM (iteration 2): removed previous nat helpers and added exec multiply function */
exec fn multiply_binary_strings(a: &[char], b: &[char]) -> Vec<char>
    requires
        ValidBitString(a@),
        ValidBitString(b@),
    ensures
        ValidBitString(result@),
        Str2Int(result@) == Str2Int(a@) * Str2Int(b@),
{
    let mut result = Vec::<char>::new();
    // initialize result with zeros, length a.len() + b.len()
    for _ in 0..(a.len() + b.len()) {
        result.push('0');
    }
    // reverse a and b to have LSB at index 0
    let mut a_rev = Vec::<char>::new();
    let mut b_rev = Vec::<char>::new();
    for &c in a.iter().rev() { a_rev.push(c); }
    for &c in b.iter().rev() { b_rev.push(c); }
    // now multiply
    for i in 0..a_rev.len() {
        if a_rev[i] == '1' {
            let mut carry = 0u8;
            for j in 0..b_rev.len() {
                let pos = i + j;
                let b_bit = (b_rev[j] == '1') as u8;
                let res_bit = (result[pos] == '1') as u8;
                let sum = b_bit + res_bit + carry;
                carry = sum / 2;
                result[pos] = if sum % 2 == 1 { '1' } else { '0' };
            }
            let mut pos = i + b_rev.len();
            while carry > 0 && pos < result.len() {
                let res_bit = (result[pos] == '1') as u8;
                let sum = res_bit + carry;
                carry = sum / 2;
                result[pos] = if sum % 2 == 1 { '1' } else { '0' };
                pos += 1;
            }
            if carry > 0 {
                result.push('1');
            }
        }
    }
    // now reverse result to MSB first
    result.reverse();
    // remove leading zeros
    while result.len() > 0 && result[0] == '0' {
        result.remove(0);
    }
    // if empty, add '0'
    if result.is_empty() {
        result.push('0');
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>

/* code modified by LLM (iteration 2): implemented multiplication using helper */
{
    let res = multiply_binary_strings(a, b);
    res
}
// </vc-code>

fn main() {}
}

