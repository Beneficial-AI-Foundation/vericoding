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
fn bit_sub(s1: &[char], s2: &[char]) -> Vec<char>
    ensures
        ValidBitString(result@),
        Str2Int(result@) == Str2Int(s1@) - Str2Int(s2@)
{
    let mut i = (s1.len() as int) - 1;
    let mut j = (s2.len() as int) - 1;
    let mut result = Vec::new();
    let mut borrow = 0;
    
    while i >= 0
        invariant
            i >= -1,
            j >= -1,
            borrow == 0 || borrow == 1,
            ValidBitString(result@),
            Str2Int(s1.subrange(i + 1, s1.len() as int)) - Str2Int(s2.subrange(j + 1, s2.len() as int)) == borrow * (pow2((i + 1) as nat)) + Str2Int(result@),
        decreases i + 1
    {
        let d1 = if i >= 0 { if s1[i as usize] == '1' { 1 } else { 0 } } else { 0 };
        let d2 = if j >= 0 { if s2[j as usize] == '1' { 1 } else { 0 } } else { 0 };
        
        let diff = d1 - d2 - borrow;
        
        if diff >= 0 {
            borrow = 0;
            result.push(if diff == 1 { '1' } else { '0' });
        } else {
            borrow = 1;
            result.push(if diff == -1 { '1' } else { '0' });
        }
        
        i = i - 1;
        j = j - 1;
    }
    
    result.reverse();
    result
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * pow2(n - 1)
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let result = bit_sub(s1, s2);
    result
}
// </vc-code>

fn main() {}
}


