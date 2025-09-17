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
/* helper modified by LLM (iteration 4): fix pow2 parameter type and add borrow lemma */
spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * pow2((n - 1) as nat)
    }
}

proof fn borrow_lemma(s1: Seq<char>, s2: Seq<char>, i: int, j: int, borrow: int, res: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        Str2Int(s1) >= Str2Int(s2),
        0 <= i && i < s1.len() as int,
        0 <= j && j < s2.len() as int,
        borrow == 0 || borrow == 1,
        ValidBitString(res)
    ensures
        Str2Int(s1.subrange(i + 1, s1.len() as int)) - Str2Int(s2.subrange(j + 1, s2.len() as int)) == borrow * pow2((i + 1) as nat) + Str2Int(res)
{
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fix type annotations and implement proper subtraction */
{
    let mut i = (s1.len() as usize) - 1;
    let mut j = (s2.len() as usize) - 1;
    let mut res = Vec::new();
    let mut borrow = 0;
    
    while i >= 0 && j >= 0
        invariant
            i <= s1.len() - 1,
            j <= s2.len() - 1,
            borrow == 0 || borrow == 1,
            ValidBitString(res@),
            Str2Int(s1@.subrange(i as int + 1, s1.len() as int)) - Str2Int(s2@.subrange(j as int + 1, s2.len() as int)) == borrow * pow2((i + 1) as nat) + Str2Int(res@)
        decreases i + 1
    {
        let d1 = if s1[i] == '1' { 1 } else { 0 };
        let d2 = if s2[j] == '1' { 1 } else { 0 };
        
        let diff = d1 - d2 - borrow;
        
        if diff >= 0 {
            borrow = 0;
            res.push(if diff == 1 { '1' } else { '0' });
        } else {
            borrow = 1;
            res.push(if diff == -1 { '1' } else { '0' });
        }
        
        if i > 0 { i -= 1; } else { break; }
        if j > 0 { j -= 1; } else { break; }
    }
    
    res.reverse();
    res
}
// </vc-code>

fn main() {}
}


