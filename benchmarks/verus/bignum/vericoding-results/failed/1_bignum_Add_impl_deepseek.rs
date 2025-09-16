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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed termination and proof assertions */
spec fn pow2(exp: nat) -> nat
    decreases exp
{
    if exp == 0 {
        1
    } else {
        2 * pow2((exp - 1) as nat)
    }
}

proof fn lemma_str2int_app(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2)
    ensures Str2Int(s1 + s2) == Str2Int(s1) * pow2(s2.len() as nat) + Str2Int(s2)
    decreases s2.len()
{
    if s2.len() == 0 {
        assert(s1 + s2 =~= s1);
        assert(pow2(0) == 1);
    } else {
        let s2_prefix = s2.subrange(0, s2.len() as int - 1);
        let last_char = s2.index(s2.len() as int - 1);
        assert(s2 =~= s2_prefix + Seq::new(1, |i| last_char));
        lemma_str2int_app(s1, s2_prefix);
        assert((s1 + s2_prefix) + Seq::new(1, |i| last_char) =~= s1 + s2);
        if last_char == '1' {
            assert(Str2Int(s1 + s2) == 2 * Str2Int(s1 + s2_prefix) + 1);
        } else {
            assert(Str2Int(s1 + s2) == 2 * Str2Int(s1 + s2_prefix) + 0);
        }
        assert(Str2Int(s1) * pow2(s2.len() as nat) + Str2Int(s2) == Str2Int(s1) * (2 * pow2((s2.len() - 1) as nat)) + Str2Int(s2));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures ValidBitString(res@), 
    Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed termination, invariant, and postcondition */
{
    let mut i: usize = s1.len();
    let mut j: usize = s2.len();
    let mut carry = 0;
    let mut res = Vec::new();
    
    while i > 0 || j > 0 || carry > 0
        invariant
            i <= s1.len(),
            j <= s2.len(),
            carry == 0 || carry == 1,
            ValidBitString(res@),
            Str2Int(res@) + carry * pow2(res.len() as nat) == Str2Int(s1@.subrange(i as int, s1.len() as int)) + Str2Int(s2@.subrange(j as int, s2.len() as int)),
        decreases i + j + carry
    {
        let mut sum = carry;
        if i > 0 {
            sum += if s1[i - 1] == '1' { 1 } else { 0 };
            i -= 1;
        }
        if j > 0 {
            sum += if s2[j - 1] == '1' { 1 } else { 0 };
            j -= 1;
        }
        
        proof {
            lemma_str2int_app(res@, Seq::new(1, |i| if sum % 2 == 1 { '1' } else { '0' }));
        }
        
        res.insert(0, if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
    }
    
    proof {
        lemma_str2int_app(Seq::empty(), res@);
    }
    
    res
}
// </vc-code>

fn main() {}
}