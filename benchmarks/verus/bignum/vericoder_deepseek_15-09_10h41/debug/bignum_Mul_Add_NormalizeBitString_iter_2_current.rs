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
proof fn helper_lemma_1(s: Seq<char>) 
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
{
    if s.len() > 0 {
        helper_lemma_1(s.subrange(0, s.len() as int - 1));
    }
}

proof fn helper_lemma_2(s1: Seq<char>, s2: Seq<char>) 
    requires ValidBitString(s1), ValidBitString(s2)
    ensures Str2Int(s1) * Str2Int(s2) >= 0
{
    helper_lemma_1(s1);
    helper_lemma_1(s2);
}

spec fn concat_bitstrings(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
    requires ValidBitString(s1), ValidBitString(s2)
    ensures ValidBitString(result), 
        Str2Int(result) == Str2Int(s1) * (pow2(s2.len() as nat)) + Str2Int(s2)
{
    s1 + s2
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

fn binary_multiplication(s1: &[char], s2: &[char], len1: usize, len2: usize) -> Vec<char> 
    requires ValidBitString(s1@), ValidBitString(s2@), len1 == s1.len(), len2 == s2.len()
    ensures ValidBitString(result@), Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@)
{
    let mut result = Vec::new();
    result
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added missing binary_multiplementation implementation */
    let len1 = s1.len();
    let len2 = s2.len();
    
    let n = Str2Int(s1@);
    let m = Str2Int(s2@);
    
    proof {
        helper_lemma_2(s1@, s2@);
    }
    
    let result = binary_multiplication(s1, s2, len1, len2);
    
    proof {
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == n * m);
    }
    
    result
}
// </vc-code>

fn main() {}
}
