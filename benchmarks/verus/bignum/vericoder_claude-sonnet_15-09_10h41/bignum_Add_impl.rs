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
/* helper modified by LLM (iteration 5): added str2int preservation lemma for reverse operation */
proof fn str2int_empty_lemma()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn str2int_subrange_lemma(s: Seq<char>, i: int)
    requires 0 <= i <= s.len(),
        ValidBitString(s)
    ensures ValidBitString(s.subrange(0, i))
{
}

proof fn str2int_monotonic_lemma(s: Seq<char>)
    requires ValidBitString(s),
        s.len() > 0
    ensures Str2Int(s) >= Str2Int(s.subrange(0, s.len() - 1))
{
}

proof fn valid_bit_string_push_lemma(s: Seq<char>, c: char)
    requires ValidBitString(s),
        c == '0' || c == '1'
    ensures ValidBitString(s.push(c))
{
}

proof fn str2int_reverse_lemma(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.reverse()) == Str2Int(s)
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let rev = s.reverse();
        assert(rev.index(0) == s.index(s.len() - 1));
        str2int_reverse_lemma(s.subrange(0, s.len() - 1));
    }
}

fn reverse_bits(bits: Vec<char>) -> (result: Vec<char>)
    requires ValidBitString(bits@)
    ensures ValidBitString(result@),
        result.len() == bits.len(),
        result@ == bits@.reverse()
{
    let mut result = Vec::<char>::new();
    let mut i = bits.len();
    
    while i > 0
        invariant
            ValidBitString(result@),
            i <= bits.len(),
            result.len() == bits.len() - i,
            result@ == bits@.subrange(i as int, bits.len() as int).reverse(),
        decreases i
    {
        i -= 1;
        result.push(bits[i]);
    }
    
    result
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
    /* code modified by LLM (iteration 5): fixed nat literal syntax errors */
    let mut result = Vec::<char>::new();
    let mut carry = 0u8;
    let mut i1 = s1.len();
    let mut i2 = s2.len();
    let mut partial_sum = 0;
    
    while i1 > 0 || i2 > 0 || carry > 0
        invariant
            ValidBitString(result@),
            carry <= 1,
            i1 <= s1.len(),
            i2 <= s2.len(),
            partial_sum + (carry as nat) == Str2Int(s1@.subrange(i1 as int, s1.len() as int)) + Str2Int(s2@.subrange(i2 as int, s2.len() as int)),
            Str2Int(result@.reverse()) == partial_sum,
        decreases i1 + i2 + carry
    {
        let bit1 = if i1 > 0 { 
            i1 -= 1;
            if s1[i1] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let bit2 = if i2 > 0 {
            i2 -= 1;
            if s2[i2] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let sum = bit1 + bit2 + carry;
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;
        
        result.push(result_bit);
        partial_sum = partial_sum * 2 + (if result_bit == '1' { 1 } else { 0 });
    }
    
    let final_result = reverse_bits(result);
    proof {
        str2int_reverse_lemma(result@);
    }
    final_result
}
// </vc-code>

fn main() {}
}