
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

proof fn lemma_str2int_nonnegative(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_str2int_nonnegative(s.subrange(0, s.len() as int - 1));
    }
}

proof fn lemma_str2int_monotonic(s: Seq<char>, t: Seq<char>)
    requires ValidBitString(s), ValidBitString(t), s.len() <= t.len()
    ensures Str2Int(s) <= Str2Int(t)
    decreases s.len()
{
    if s.len() == 0 {
        lemma_str2int_nonnegative(t);
    } else {
        lemma_str2int_monotonic(s.subrange(0, s.len() as int - 1), t.subrange(0, t.len() as int - 1));
    }
}

proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_str2int_append_zero(s.subrange(0, s.len() as int - 1));
    }
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_str2int_append_one(s.subrange(0, s.len() as int - 1));
    }
}

// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_Add_DivMod_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut carry = 0;
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    
    let mut i = 0;
    while i < max_len || carry > 0
        invariant
            0 <= i && i <= max_len,
            carry >= 0 && carry <= 1,
            ValidBitString(result@),
            result.len() == i,
            Str2Int(result@) + carry * (1 << i) == Str2Int(a@) + Str2Int(b@)
    {
        let a_bit = if i < a.len() && a[i] == '1' { 1 } else { 0 };
        let b_bit = if i < b.len() && b[i] == '1' { 1 } else { 0 };
        let sum = a_bit + b_bit + carry;
        
        if sum % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        
        carry = sum / 2;
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}

