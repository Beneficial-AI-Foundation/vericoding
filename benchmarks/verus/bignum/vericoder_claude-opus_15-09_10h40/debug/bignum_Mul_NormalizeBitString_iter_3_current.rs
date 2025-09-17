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
proof fn lemma_str2int_empty()
    ensures Str2Int(seq![]) == 0
{
}

proof fn lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{
    assert(seq!['0'].subrange(0, 0) =~= seq![]);
}

proof fn lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{
    assert(seq!['1'].subrange(0, 0) =~= seq![]);
}

proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
{
    let s_new = s.push('0');
    assert(s_new.subrange(0, s_new.len() - 1) =~= s);
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
    let s_new = s.push('1');
    assert(s_new.subrange(0, s_new.len() - 1) =~= s);
}

/* helper modified by LLM (iteration 3): Fixed add_binary_strings parameter type */
exec fn add_binary_strings(s1: &[char], s2: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
{
    let mut result = Vec::<char>::new();
    let mut carry = 0u8;
    let mut i = 0;
    
    while i < s1.len() || i < s2.len() || carry > 0
        invariant
            i <= s1.len(),
            i <= s2.len(),
            carry <= 1,
            ValidBitString(result@),
            Str2Int(result@) + (carry as nat) * pow2(i as nat) == 
                Str2Int(s1@.subrange(0, i as int)) + Str2Int(s2@.subrange(0, i as int))
    {
        let bit1 = if i < s1.len() { if s1[i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let bit2 = if i < s2.len() { if s2[i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let sum = bit1 + bit2 + carry;
        
        if sum % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        
        carry = sum / 2;
        i = i + 1;
    }
    
    result
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed type mismatch by using slices consistently */
    let mut result = Vec::<char>::new();
    result.push('0');
    proof {
        lemma_str2int_single_zero();
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == 0);
    }
    
    let mut i = 0;
    while i < s2.len()
        invariant
            0 <= i <= s2.len(),
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@.subrange(0, i as int))
    {
        let mut temp = result.clone();
        if s2[i] == '1' {
            temp = add_binary_strings(&temp[..], s1);
        }
        
        if i + 1 < s2.len() {
            let mut doubled = Vec::<char>::new();
            doubled.push('0');
            for j in 0..temp.len()
                invariant
                    0 <= j <= temp.len(),
                    doubled.len() == j + 1,
                    ValidBitString(doubled@),
                    ValidBitString(temp@)
            {
                doubled.push(temp[j]);
            }
            proof {
                lemma_str2int_append_zero(temp@);
            }
            result = doubled;
        } else {
            result = temp;
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}
