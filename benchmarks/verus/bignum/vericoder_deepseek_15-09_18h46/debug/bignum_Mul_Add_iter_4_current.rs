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
/* helper modified by LLM (iteration 4): Fixed concat spec function and added result variable */
spec fn concat(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
    requires ValidBitString(s1), ValidBitString(s2)
    ensures ValidBitString(result), Str2Int(result) == Str2Int(s1) * pow2(s2.len()) + Str2Int(s2)
{
    s1 + s2
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn helper_lemma_pow2_zero()
    ensures pow2(0) == 1
{
}

proof fn helper_lemma_pow2_succ(n: nat)
    ensures pow2(n + 1) == 2 * pow2(n)
{
}

proof fn helper_lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s + Seq::new().push('0')) == 2 * Str2Int(s)
{
}

proof fn helper_lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s + Seq::new().push('1')) == 2 * Str2Int(s) + 1
{
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed compilation error and refined verification */
{
    let mut result = Vec::<char>::new();
    let mut s1_copy = s1.to_vec();
    let mut s2_copy = s2.to_vec();
    
    while !s2_copy.is_empty()
        invariant
            ValidBitString(result@),
            ValidBitString(s1_copy@),
            ValidBitString(s2_copy@),
            Str2Int(result@) * pow2(s2_copy.len()) + Str2Int(s1_copy@) * Str2Int(s2_copy@) == Str2Int(s1@) * Str2Int(s2@)
        decreases s2_copy.len()
    {
        let last_char = s2_copy.pop().unwrap();
        
        if last_char == '1' {
            let mut new_result = Vec::new();
            new_result.extend_from_slice(&result);
            new_result.extend_from_slice(&s1_copy);
            result = new_result;
        } else {
            let mut new_result = Vec::new();
            new_result.extend_from_slice(&result);
            result = new_result;
            proof {
                helper_lemma_str2int_append_zero(result@);
            }
        }
        
        let mut new_s1 = Vec::new();
        new_s1.push('0');
        new_s1.extend_from_slice(&s1_copy);
        s1_copy = new_s1;
    }
    
    result
}
// </vc-code>

fn main() {}
}
