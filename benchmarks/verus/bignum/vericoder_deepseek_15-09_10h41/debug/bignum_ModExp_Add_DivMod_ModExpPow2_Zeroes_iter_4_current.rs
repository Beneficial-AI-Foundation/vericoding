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
proof fn indexing_lemma(v: &[char], i: usize)
    requires i < v@.len()
    ensures v@.index(i as int) == v[i]
{
    /* helper modified by LLM (iteration 4): Fixed type conversion */
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed indexing with proper type conversion */
    let mut res = Vec::<char>::new();
    let a_len = a.len();
    let b_len = b.len();
    
    if a_len == 0 {
        res.extend_from_slice(b);
        return res;
    }
    if b_len == 0 {
        res.extend_from_slice(a);
        return res;
    }
    
    let max_len = if a_len > b_len { a_len } else { b_len };
    let mut carry = 0;
    
    for i in 0..max_len {
        assert(i < a_len ==> i < a@.len());
        assert(i < b_len ==> i < b@.len());
        
        let a_digit = if i < a_len { if a[i] == '1' { 1 } else { 0 } } else { 0 };
        let b_digit = if i < b_len { if b[i] == '1' { 1 } else { 0 } } else { 0 };
        let sum = a_digit + b_digit + carry;
        
        if sum % 2 == 0 {
            res.push('0');
        } else {
            res.push('1');
        }
        
        carry = sum / 2;
    }
    
    if carry > 0 {
        res.push('1');
    }
    
    res
}
// </vc-code>

fn main() {}
}

