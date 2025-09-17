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
proof fn helper_lemma_mul(s1: Seq<char>, s2: Seq<char>, i: int)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        0 <= i && i <= s2.len() as int,
    ensures
        Str2Int(s1) * Str2Int(s2.subrange(0, i)) == Str2Int(s1) * Str2Int(s2.subrange(0, i)),
    decreases s2.len() as int - i
{
    if i > 0 {
        helper_lemma_mul(s1, s2, i - 1);
    }
}

proof fn helper_lemma_append(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })
{
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<char>::new();
    let mut temp = Vec::<char>::new();
    
    let mut i = 0;
    while i < s2.len()
        invariant
            ValidBitString(result@),
            ValidBitString(temp@),
            Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@.subrange(0, i as int)),
            i <= s2.len(),
    {
        let bit = s2[i];
        if bit == '1' {
            let mut j = 0;
            while j < s1.len()
                invariant
                    ValidBitString(temp@),
                    temp@.len() == j as nat,
                    forall |k: int| 0 <= k && k < j ==> temp@[k] == s1@[k],
                    j <= s1.len(),
            {
                temp.push(s1[j]);
                j += 1;
            }
        } else {
            let mut j = 0;
            while j < s1.len()
                invariant
                    ValidBitString(temp@),
                    temp@.len() == j as nat,
                    forall |k: int| 0 <= k && k < j ==> temp@[k] == '0',
                    j <= s1.len(),
            {
                temp.push('0');
                j += 1;
            }
        }
        
        result.push('0');
        let mut k = 0;
        while k < temp.len()
            invariant
                ValidBitString(result@),
                ValidBitString(temp@),
                Str2Int(result@) == 2 * Str2Int(old(result)@) + Str2Int(temp@),
                k <= temp.len(),
        {
            result.push(temp[k]);
            k += 1;
        }
        
        temp.clear();
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}
