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
/* helper modified by LLM (iteration 10): Fixed add_binary to accept slice parameter and added pow2 spec function */
proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s.push('0')) == 2 * Str2Int(s)
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
    let s = seq!['0'];
    assert(s.len() == 1);
    let empty: Seq<char> = seq![];
    assert(s.subrange(0, 0) == empty);
    assert(Str2Int(empty) == 0);
    assert(s.index(0) == '0');
}

proof fn lemma_str2int_one()
    ensures
        Str2Int(seq!['1']) == 1
{
    let s = seq!['1'];
    assert(s.len() == 1);
    let empty: Seq<char> = seq![];
    assert(s.subrange(0, 0) == empty);
    assert(Str2Int(empty) == 0);
    assert(s.index(0) == '1');
}

exec fn add_binary(a: &[char], b: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(a@),
        ValidBitString(b@)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(a@) + Str2Int(b@)
{
    let mut result = Vec::<char>::new();
    let mut carry = 0u8;
    let mut i: usize = 0;
    
    while i < a.len() || i < b.len() || carry > 0
        invariant
            i <= a.len(),
            i <= b.len(),
            carry <= 1,
            ValidBitString(result@),
            Str2Int(result@) + (carry as nat) * pow2(i as nat) == 
                Str2Int(a@.subrange(0, i as int)) + Str2Int(b@.subrange(0, i as int))
    {
        let a_bit = if i < a.len() { if a[i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let b_bit = if i < b.len() { if b[i] == '1' { 1u8 } else { 0u8 } } else { 0u8 };
        let sum = a_bit + b_bit + carry;
        result.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        i = i + 1;
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}

spec fn pow2(n: nat) -> nat
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Use as_slice() method to convert Vec to slice */
    let mut result = Vec::<char>::new();
    result.push('0');
    
    proof {
        lemma_str2int_zero();
    }
    
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@.subrange(0, i as int)) * Str2Int(s2@)
    {
        let mut temp = Vec::<char>::new();
        let mut j: usize = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                ValidBitString(temp@),
                Str2Int(temp@) == 2 * Str2Int(result@.subrange(0, j as int))
        {
            temp.push('0');
            proof {
                lemma_str2int_append_zero(result@.subrange(0, j as int));
            }
            j = j + 1;
        }
        
        if s1[i] == '1' {
            temp = add_binary(temp.as_slice(), s2);
        }
        
        result = temp;
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}
