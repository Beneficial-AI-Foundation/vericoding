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
/* helper modified by LLM (iteration 6): fixed add_binary arithmetic and added lemmas for proof */
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

proof fn lemma_str2int_zero()
    ensures Str2Int(seq!['0']) == 0
{
    assert(seq!['0'].len() == 1);
    assert(seq!['0'].subrange(0, 0) =~= Seq::<char>::empty());
    assert(Str2Int(Seq::<char>::empty()) == 0);
    assert(seq!['0'][0] == '0');
}

exec fn add_binary(s1: &[char], s2: &[char]) -> (result: Vec<char>)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
    ensures
        ValidBitString(result@),
        Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@),
{
    let mut result = Vec::<char>::new();
    let mut carry: u8 = 0;
    let mut i: usize = 0;
    
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len || carry > 0
        invariant
            0 <= i,
            i <= max_len + 1,
            carry <= 1,
            ValidBitString(result@),
        decreases
            if i < max_len { max_len - i } else { 0 } + if carry > 0 { 1 } else { 0 }
    {
        let mut sum: u8 = carry;
        
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
        
        if i < max_len {
            i = i + 1;
        } else {
            assert(carry == 0);
            break;
        }
    }
    
    let mut reversed = Vec::<char>::new();
    let mut j: usize = result.len();
    while j > 0
        invariant
            0 <= j,
            j <= result.len(),
            ValidBitString(result@),
            ValidBitString(reversed@),
            reversed.len() == result.len() - j,
            forall |k: int| 0 <= k && k < reversed.len() ==> reversed@[k] == result@[result.len() - 1 - k],
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
    /* code modified by LLM (iteration 6): fixed zero checks and ValidBitString maintenance */
    if s2.len() == 0 || (s2.len() == 1 && s2[0] == '0') {
        let mut result = Vec::<char>::new();
        result.push('0');
        proof {
            assert(ValidBitString(result@));
            assert(result@.len() == 1);
            assert(result@[0] == '0');
            lemma_str2int_zero();
            assert(Str2Int(result@) == 0);
            if s2.len() == 0 {
                assert(Str2Int(s2@) == 0);
            } else {
                assert(s2.len() == 1);
                assert(s2[0] == '0');
                assert(s2@.len() == 1);
                assert(s2@[0] == '0');
                lemma_str2int_zero();
                assert(Str2Int(seq!['0']) == 0);
            }
            assert(Str2Int(s1@) * 0 == 0);
        }
        return result;
    }
    
    if s1.len() == 0 || (s1.len() == 1 && s1[0] == '0') {
        let mut result = Vec::<char>::new();
        result.push('0');
        proof {
            assert(ValidBitString(result@));
            lemma_str2int_zero();
            assert(Str2Int(result@) == 0);
            if s1.len() == 0 {
                assert(Str2Int(s1@) == 0);
            } else {
                assert(s1.len() == 1);
                assert(s1[0] == '0');
                lemma_str2int_zero();
            }
            assert(0 * Str2Int(s2@) == 0);
        }
        return result;
    }
    
    let mut result = Vec::<char>::new();
    result.push('0');
    
    let mut shifted_s1 = Vec::<char>::new();
    let mut k: usize = 0;
    while k < s1.len()
        invariant
            0 <= k,
            k <= s1.len(),
            shifted_s1.len() == k,
            ValidBitString(s1@),
            forall |j: int| 0 <= j && j < k ==> shifted_s1@[j] == s1@[j],
            forall |j: int| 0 <= j && j < k ==> (shifted_s1@[j] == '0' || shifted_s1@[j] == '1'),
        decreases s1.len() - k
    {
        shifted_s1.push(s1[k]);
        k = k + 1;
    }
    
    proof {
        assert(shifted_s1@.len() == s1@.len());
        assert(forall |j: int| 0 <= j && j < shifted_s1@.len() ==> shifted_s1@[j] == s1@[j]);
        assert(ValidBitString(shifted_s1@));
    }
    
    let mut i: usize = s2.len();
    
    while i > 0
        invariant
            0 <= i,
            i <= s2.len(),
            ValidBitString(result@),
            ValidBitString(shifted_s1@),
        decreases i
    {
        i = i - 1;
        
        if s2[i] == '1' {
            result = add_binary(&result, &shifted_s1);
        }
        
        if i > 0 {
            shifted_s1.push('0');
            proof {
                assert(forall |j: int| 0 <= j && j < shifted_s1@.len() - 1 ==> 
                    (shifted_s1@[j] == '0' || shifted_s1@[j] == '1'));
                assert(shifted_s1@[shifted_s1@.len() - 1] == '0');
                assert(ValidBitString(shifted_s1@));
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}


