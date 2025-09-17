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
/* helper modified by LLM (iteration 7): Add decreases clauses to proofs */
proof fn str2int_recursive(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
    decreases s.len()
{
}

spec fn non_empty(s: Seq<char>) -> bool { s.len() > 0 }

proof fn str2int_empty() -> (ret: nat)
    ensures ret == 0
{
   0
}

proof fn str2int_monotonic(s: Seq<char>, i: int)
    requires ValidBitString(s), 0 <= i && i < s.len() as int
    ensures Str2Int(s.subrange(0, i)) <= Str2Int(s)
    decreases s.len()
{
}

spec fn msb(s: Seq<char>) -> char
{
    s.index(s.len() as int - 1)
}

spec fn lsb(s: Seq<char>) -> char
{
    s.index(0)
}

spec fn concat_valid(a: Seq<char>, b: Seq<char>) -> bool
{
    true
}

spec fn is_valid_bit(c: char) -> bool {
    c == '0' || c == '1'
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): Add decreases clause to while loop */
{
    let mut res = Vec::<char>::new();
    let mut carry = false;
    let len_a = a.len();
    let len_b = b.len();
    let max_len = if len_a > len_b { len_a } else { len_b };
    
    let mut i = 0;
    while i < max_len
        invariant
            0 <= i,
            res@.len() == i,
            ValidBitString(res@),
            i <= max_len
        decreases max_len - i
    {
        let bit_a = if i < len_a { a[i] } else { '0' };
        let bit_b = if i < len_b { b[i] } else { '0' };
        let (sum, new_carry) = match (bit_a, bit_b, carry) {
            ('0', '0', false) => ('0', false),
            ('0', '0', true) => ('1', false),
            ('0', '1', false) => ('1', false),
            ('0', '1', true) => ('0', true),
            ('1', '0', false) => ('1', false),
            ('1', '0', true) => ('0', true),
            ('1', '1', false) => ('0', true),
            ('1', '1', true) => ('1', true),
            (_, _, _) => ('0', false)
        };
        res.push(sum);
        carry = new_carry;
        i += 1;
    }
    if carry {
        res.push('1');
    }
    res
}
// </vc-code>

fn main() {}
}

