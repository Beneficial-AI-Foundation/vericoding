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
/* helper modified by LLM (iteration 5): fixed index bounds checks and postcondition */
proof fn lemma_str2int_bounds(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < pow2(s.len() as nat)
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_str2int_bounds(s.subrange(0, s.len() as int - 1));
    }
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * pow2((n - 1) as nat)
    }
}

exec fn add_binary_strings(a: &[char], b: &[char]) -> (res: Vec<char>)
    requires ValidBitString(a@),
        ValidBitString(b@)
    ensures ValidBitString(res@),
        res@.len() <= if a@.len() >= b@.len() { a@.len() + 1 } else { b@.len() + 1 },
        Str2Int(res@) == (Str2Int(a@) + Str2Int(b@)) % pow2(res@.len() as nat)
{
    let mut carry = 0u8;
    let mut result = Vec::new();
    let mut i: usize = 0;
    let a_len = a.len();
    let b_len = b.len();
    let max_len = if a_len >= b_len { a_len } else { b_len };
    
    while i < max_len || carry != 0
        invariant
            i <= max_len,
            carry <= 1,
            ValidBitString(result@),
            result@.len() == i,
            i <= usize::MAX - 1,
        decreases max_len + 1 - i + carry
    {
        let mut sum = carry;
        if i < a_len {
            if a_len - 1 - i < a_len && a[a_len - 1 - i] == '1' {
                sum = sum + 1;
            }
        }
        if i < b_len {
            if b_len - 1 - i < b_len && b[b_len - 1 - i] == '1' {
                sum = sum + 1;
            }
        }
        
        if sum % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        carry = sum / 2;
        i = i + 1;
    }
    
    let mut j: usize = 0;
    let mut reversed = Vec::new();
    let result_len = result.len();
    while j < result_len
        invariant
            j <= result_len,
            ValidBitString(result@),
            ValidBitString(reversed@),
            reversed@.len() == j,
            forall |k: int| 0 <= k && k < j ==> {
                k < reversed@.len() &&
                result_len - 1 - k >= 0 &&
                result_len - 1 - k < result@.len() &&
                reversed@[k] == result@[result_len - 1 - k]
            },
        decreases result_len - j
    {
        if result_len - 1 - j < result_len {
            reversed.push(result[result_len - 1 - j]);
        }
        j = j + 1;
    }
    
    reversed
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): calling helper function */
    add_binary_strings(a, b)
}
// </vc-code>

fn main() {}
}

