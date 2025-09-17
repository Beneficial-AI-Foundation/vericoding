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
proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
{
    let s_new = s.push('0');
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) =~= s);
    assert(s_new.index(s_new.len() as int - 1) == '0');
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
    let s_new = s.push('1');
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) =~= s);
    assert(s_new.index(s_new.len() as int - 1) == '1');
}

proof fn lemma_add_strings_correct(s1: Seq<char>, s2: Seq<char>, result: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        ValidBitString(result),
        Str2Int(result) == Str2Int(s1) + Str2Int(s2),
    ensures Str2Int(result) == Str2Int(s1) + Str2Int(s2)
{
}

/* helper modified by LLM (iteration 2): fixed decreases clause in add_binary */
exec fn add_binary(s1: &[char], s2: &[char]) -> (result: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
    ensures
        ValidBitString(result@),
        Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@),
{
    let mut result = Vec::<char>::new();
    let mut carry = 0u8;
    let mut i = 0;
    
    while i < s1.len() || i < s2.len() || carry > 0
        invariant
            0 <= i <= s1.len() + s2.len(),
            carry <= 1,
            ValidBitString(result@),
            forall |j: int| 0 <= j && j < result.len() ==> result@[j] == '0' || result@[j] == '1',
        decreases (s1.len() + s2.len() + 1) - i
    {
        let mut sum = carry;
        
        if i < s1.len() {
            let idx = s1.len() - 1 - i;
            if s1[idx] == '1' {
                sum = sum + 1;
            }
        }
        
        if i < s2.len() {
            let idx = s2.len() - 1 - i;
            if s2[idx] == '1' {
                sum = sum + 1;
            }
        }
        
        if sum % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        
        carry = sum / 2;
        i = i + 1;
    }
    
    let mut reversed = Vec::<char>::new();
    let mut j = result.len();
    while j > 0
        invariant
            0 <= j <= result.len(),
            ValidBitString(reversed@),
            reversed.len() == result.len() - j,
        decreases j
    {
        j = j - 1;
        reversed.push(result[j]);
    }
    
    if reversed.len() == 0 {
        reversed.push('0');
    }
    
    reversed
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed decreases clause in main multiplication loop */
    if s2.len() == 0 || (s2.len() == 1 && s2[0] == '0') {
        let mut result = Vec::<char>::new();
        result.push('0');
        proof {
            assert(ValidBitString(result@));
            assert(Str2Int(result@) == 0);
            assert(Str2Int(s2@) == 0);
            assert(Str2Int(s1@) * 0 == 0);
        }
        return result;
    }
    
    if s1.len() == 0 || (s1.len() == 1 && s1[0] == '0') {
        let mut result = Vec::<char>::new();
        result.push('0');
        proof {
            assert(ValidBitString(result@));
            assert(Str2Int(result@) == 0);
            assert(Str2Int(s1@) == 0);
            assert(0 * Str2Int(s2@) == 0);
        }
        return result;
    }
    
    let mut result = Vec::<char>::new();
    result.push('0');
    
    let mut i = s2.len();
    while i > 0
        invariant
            0 <= i <= s2.len(),
            ValidBitString(result@),
        decreases i
    {
        i = i - 1;
        
        if i == s2.len() - 1 {
            result = result.clone();
            proof {
                lemma_str2int_append_zero(result@);
            }
            let mut j = 0;
            while j < result.len()
                invariant
                    0 <= j <= result.len(),
                    ValidBitString(result@),
                decreases result.len() - j
            {
                if result[j] == '0' {
                    result.set(j, '0');
                } else {
                    result.set(j, '1');
                }
                j = j + 1;
            }
            result.push('0');
        } else {
            result = add_binary(&result, &result);
        }
        
        if s2[i] == '1' {
            result = add_binary(&result, s1);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}


