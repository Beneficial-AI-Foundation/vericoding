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
/* helper modified by LLM (iteration 7): fixed assertion to avoid failing proof */
proof fn str2int_subrange_property(s: Seq<char>, i: int)
{
    assert(ValidBitString(s) && 0 <= i <= s.len() ==> ValidBitString(s.subrange(0, i))) by {
        if ValidBitString(s) && 0 <= i <= s.len() {
            assert(forall |k: int| #![auto] 0 <= k < i ==> (s.subrange(0, i).index(k) == s.index(k)));
        }
    };
}

proof fn str2int_empty_lemma()
{
    assert(Str2Int(Seq::<char>::empty()) == 0);
}

proof fn str2int_single_lemma(c: char)
    requires c == '0' || c == '1'
{
    assert(Str2Int(seq![c]) == (if c == '1' { 1nat } else { 0nat })) by {
        let s = seq![c];
        assert(s.len() == 1);
        assert(s.subrange(0, 0).len() == 0);
        assert(Str2Int(s.subrange(0, 0)) == 0);
        assert(s.index(0) == c);
    };
}

proof fn str2int_concat_lemma(s1: Seq<char>, s2: Seq<char>)
{
    assert((ValidBitString(s1) && ValidBitString(s2)) ==> ValidBitString(s1 + s2)) by {
        if ValidBitString(s1) && ValidBitString(s2) {
            assert(forall |i: int| 0 <= i < (s1 + s2).len() ==> 
                ((s1 + s2).index(i) == '0' || (s1 + s2).index(i) == '1'));
        }
    };
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn str2int_shift_lemma(s: Seq<char>, bit: char)
{
    assert((ValidBitString(s) && (bit == '0' || bit == '1')) ==> 
        (ValidBitString(s + seq![bit]) && 
         Str2Int(s + seq![bit]) == 2 * Str2Int(s) + (if bit == '1' { 1nat } else { 0nat }))) by {
        if ValidBitString(s) && (bit == '0' || bit == '1') {
            let extended = s + seq![bit];
            assert(extended.len() == s.len() + 1);
            assert(extended.subrange(0, extended.len() - 1) =~= s);
            assert(extended.index(extended.len() - 1) == bit);
        }
    };
}

proof fn str2int_le_sum_lemma(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1),
             ValidBitString(s2)
    ensures Str2Int(s1) + Str2Int(s2) >= Str2Int(s1),
            Str2Int(s1) + Str2Int(s2) >= Str2Int(s2)
{
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
{
    /* code modified by LLM (iteration 7): fixed decreases clause and overflow issues */
    let mut result = Vec::<char>::new();
    let mut carry = 0u8;
    let mut i: usize = 0;
    
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len || carry > 0
        invariant
            ValidBitString(result@),
            carry <= 1,
            i <= max_len + 1,
            i < usize::MAX
        decreases (max_len + 1 - i) + carry as usize
    {
        let bit1 = if i < s1.len() && s1[s1.len() - 1 - i] == '1' { 1u8 } else { 0u8 };
        let bit2 = if i < s2.len() && s2[s2.len() - 1 - i] == '1' { 1u8 } else { 0u8 };
        
        let sum = bit1 + bit2 + carry;
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;
        
        result.push(result_bit);
        i = i + 1;
        
        proof {
            str2int_single_lemma(result_bit);
        }
    }
    
    let mut final_result = Vec::<char>::new();
    let mut j = result.len();
    
    while j > 0
        invariant
            ValidBitString(final_result@),
            j <= result.len(),
            ValidBitString(result@)
        decreases j
    {
        j = j - 1;
        final_result.push(result[j]);
        
        proof {
            str2int_single_lemma(result@[j as int]);
        }
    }
    
    if final_result.len() == 0 {
        final_result.push('0');
        proof {
            str2int_single_lemma('0');
        }
    }
    
    proof {
        str2int_le_sum_lemma(s1@, s2@);
        assert(Str2Int(final_result@) == Str2Int(s1@) + Str2Int(s2@));
    }
    
    final_result
}
// </vc-code>

fn main() {}
}