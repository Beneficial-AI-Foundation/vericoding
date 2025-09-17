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
    requires
        ValidBitString(s)
    ensures
        Str2Int(s.push('0')) == 2 * Str2Int(s)
    decreases s.len()
{
    let s_new = s.push('0');
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) == s);
    assert(s_new.index(s_new.len() as int - 1) == '0');
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
    decreases s.len()
{
    let s_new = s.push('1');
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) == s);
    assert(s_new.index(s_new.len() as int - 1) == '1');
}

proof fn lemma_str2int_zero()
    ensures
        Str2Int(seq!['0']) == 0
{
    assert(seq!['0'].len() == 1);
    assert(seq!['0'].subrange(0, 0) == seq![]);
    assert(Str2Int(seq![]) == 0);
}

proof fn lemma_str2int_one()
    ensures
        Str2Int(seq!['1']) == 1
{
    assert(seq!['1'].len() == 1);
    assert(seq!['1'].subrange(0, 0) == seq![]);
    assert(Str2Int(seq![]) == 0);
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<char>::new();
    
    if s1.len() == 0 || s2.len() == 0 {
        result.push('0');
        proof {
            lemma_str2int_zero();
            if s1.len() == 0 {
                assert(s1@ == seq![]);
                assert(Str2Int(s1@) == 0);
            }
            if s2.len() == 0 {
                assert(s2@ == seq![]);
                assert(Str2Int(s2@) == 0);
            }
            assert(Str2Int(result@) == 0);
            assert(Str2Int(s1@) * Str2Int(s2@) == 0);
        }
        return result;
    }
    
    if s1.len() == 1 && s1[0] == '0' {
        result.push('0');
        proof {
            lemma_str2int_zero();
            assert(Str2Int(result@) == 0);
            assert(Str2Int(s1@) == 0);
            assert(Str2Int(s1@) * Str2Int(s2@) == 0);
        }
        return result;
    }
    
    if s2.len() == 1 && s2[0] == '0' {
        result.push('0');
        proof {
            lemma_str2int_zero();
            assert(Str2Int(result@) == 0);
            assert(Str2Int(s2@) == 0);
            assert(Str2Int(s1@) * Str2Int(s2@) == 0);
        }
        return result;
    }
    
    if s1.len() == 1 && s1[0] == '1' {
        let mut i = 0;
        while i < s2.len()
            invariant
                0 <= i <= s2.len(),
                result@.len() == i,
                ValidBitString(result@),
                forall |j: int| 0 <= j && j < i ==> result@[j] == s2@[j]
        {
            result.push(s2[i]);
            i = i + 1;
        }
        proof {
            lemma_str2int_one();
            assert(result@ == s2@);
            assert(Str2Int(s1@) == 1);
            assert(Str2Int(result@) == Str2Int(s2@));
            assert(Str2Int(s1@) * Str2Int(s2@) == Str2Int(s2@));
        }
        return result;
    }
    
    if s2.len() == 1 && s2[0] == '1' {
        let mut i = 0;
        while i < s1.len()
            invariant
                0 <= i <= s1.len(),
                result@.len() == i,
                ValidBitString(result@),
                forall |j: int| 0 <= j && j < i ==> result@[j] == s1@[j]
        {
            result.push(s1[i]);
            i = i + 1;
        }
        proof {
            lemma_str2int_one();
            assert(result@ == s1@);
            assert(Str2Int(s2@) == 1);
            assert(Str2Int(result@) == Str2Int(s1@));
            assert(Str2Int(s1@) * Str2Int(s2@) == Str2Int(s1@));
        }
        return result;
    }
    
    let mut acc = Vec::<char>::new();
    acc.push('0');
    
    let mut j = (s2.len() - 1) as usize;
    loop
        invariant
            j < s2.len(),
            ValidBitString(acc@),
            Str2Int(acc@) == Str2Int(s2@.subrange(j as int, s2.len() as int)) * Str2Int(s1@)
        decreases j
    {
        let mut shifted = Vec::<char>::new();
        let mut k = 0;
        while k < acc.len()
            invariant
                0 <= k <= acc.len(),
                shifted@.len() == k,
                ValidBitString(shifted@),
                forall |i: int| 0 <= i && i < k ==> shifted@[i] == acc@[i]
        {
            shifted.push(acc[k]);
            k = k + 1;
        }
        shifted.push('0');
        
        proof {
            lemma_str2int_append_zero(acc@);
            assert(shifted@ == acc@.push('0'));
            assert(Str2Int(shifted@) == 2 * Str2Int(acc@));
        }
        
        if s2[j] == '1' {
            let mut sum = Vec::<char>::new();
            let mut carry = 0u8;
            let mut p = (s1.len() - 1) as usize;
            let mut q = (shifted.len() - 1) as usize;
            
            loop
                invariant
                    p < s1.len(),
                    q < shifted.len(),
                    carry <= 1,
                    ValidBitString(sum@)
                decreases p + q
            {
                let bit1 = if p < s1.len() { if s1[p] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
                let bit2 = if q < shifted.len() { if shifted[q] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
                let s = bit1 + bit2 + carry;
                sum.push(if s % 2 == 1 { '1' } else { '0' });
                carry = s / 2;
                
                if p > 0 { p = p - 1; } else { p = s1.len(); }
                if q > 0 { q = q - 1; } else { q = shifted.len(); }
                
                if p >= s1.len() && q >= shifted.len() {
                    if carry == 1 {
                        sum.push('1');
                    }
                    break;
                }
            }
            
            acc = Vec::<char>::new();
            let mut r = (sum.len() - 1) as usize;
            loop
                invariant
                    r < sum.len(),
                    ValidBitString(acc@)
                decreases r
            {
                acc.push(sum[r]);
                if r == 0 { break; }
                r = r - 1;
            }
        } else {
            acc = shifted;
        }
        
        if j == 0 { break; }
        j = j - 1;
    }
    
    result = acc;
    result
}
// </vc-code>

fn main() {}
}
