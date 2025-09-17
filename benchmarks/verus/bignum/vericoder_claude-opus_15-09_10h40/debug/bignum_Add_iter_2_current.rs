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
spec fn power2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * power2((n - 1) as nat) }
}

proof fn lemma_str2int_bounds(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < power2(s.len() as nat)
    decreases s.len()
{
    if s.len() > 0 {
        lemma_str2int_bounds(s.subrange(0, s.len() as int - 1));
    }
}

proof fn lemma_str2int_append(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        ValidBitString(s.push(c)),
        Str2Int(s.push(c)) == 2 * Str2Int(s) + if c == '1' { 1nat } else { 0nat },
    decreases s.len()
{
    let s_new = s.push(c);
    assert(s_new.subrange(0, s_new.len() as int - 1) =~= s);
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
    /* code modified by LLM (iteration 2): Fixed type issues with power2 and nat literals */
    let mut result = Vec::<char>::new();
    let mut carry: u8 = 0;
    let mut i: usize = 0;
    let n1 = s1.len();
    let n2 = s2.len();
    let max_len = if n1 > n2 { n1 } else { n2 };
    
    while i < max_len || carry > 0
        invariant
            i <= max_len,
            carry <= 1,
            ValidBitString(result@),
            Str2Int(result@) == (Str2Int(s1@.subrange(n1 as int - i as int, n1 as int)) + Str2Int(s2@.subrange(n2 as int - i as int, n2 as int)) + carry as nat) % power2(i as nat),
    {
        let mut bit_sum = carry;
        
        if i < n1 {
            let idx1 = n1 - 1 - i;
            if s1[idx1] == '1' {
                bit_sum = bit_sum + 1;
            }
        }
        
        if i < n2 {
            let idx2 = n2 - 1 - i;
            if s2[idx2] == '1' {
                bit_sum = bit_sum + 1;
            }
        }
        
        let res_bit = if bit_sum % 2 == 1 { '1' } else { '0' };
        carry = bit_sum / 2;
        
        proof {
            let old_result = result@;
            let new_result = old_result.push(res_bit);
            lemma_str2int_append(old_result, res_bit);
            
            if i < n1 && i < n2 {
                assert(s1@.subrange(n1 as int - (i + 1) as int, n1 as int).len() == (i + 1) as int);
                assert(s2@.subrange(n2 as int - (i + 1) as int, n2 as int).len() == (i + 1) as int);
            }
        }
        
        result.push(res_bit);
        i = i + 1;
    }
    
    let mut reversed = Vec::<char>::new();
    let mut j: usize = result.len();
    
    while j > 0
        invariant
            j <= result.len(),
            ValidBitString(reversed@),
            reversed@.len() == result.len() - j,
            forall |k: int| 0 <= k && k < reversed@.len() as int ==> reversed@[k] == result@[result.len() as int - 1 - k],
    {
        j = j - 1;
        reversed.push(result[j]);
    }
    
    proof {
        assert(Str2Int(s1@.subrange(0, n1 as int)) == Str2Int(s1@));
        assert(Str2Int(s2@.subrange(0, n2 as int)) == Str2Int(s2@));
        assert(carry == 0);
    }
    
    reversed
}
// </vc-code>

fn main() {}
}