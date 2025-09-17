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
proof fn Str2Int_nonnegative(s: Seq<char>) 
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
    decreases s.len()
{
    if s.len() > 0 {
        Str2Int_nonnegative(s.subrange(0, s.len() as int - 1));
    }
}

proof fn Str2Int_len_nonnegative() 
    ensures forall |s: Seq<char>| ValidBitString(s) ==> Str2Int(s) >= 0
{
    assert forall |s: Seq<char>| ValidBitString(s) implies Str2Int(s) >= 0 by {
        Str2Int_nonnegative(s);
    };
}

fn max(a: usize, b: usize) -> usize { if a > b { a } else { b } }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let len = max(a.len(), b.len());
    let mut res = Vec::<char>::new();
    let mut carry = 0;
    
    proof {
        Str2Int_len_nonnegative();
    }
    
    let mut i = 0;
    while i < len
        invariant
            0 <= i && i <= len,
            res@.len() == i,
            ValidBitString(res@),
        decreases len - i
    {
        let a_bit = if i < a.len() && a[i] == '1' { 1 } else { 0 };
        let b_bit = if i < b.len() && b[i] == '1' { 1 } else { 0 };
        let sum = a_bit + b_bit + carry;
        
        res.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        i += 1;
    }
    
    if carry > 0 {
        res.push('1');
    }
    
    res
}
// </vc-code>

fn main() {}
}

