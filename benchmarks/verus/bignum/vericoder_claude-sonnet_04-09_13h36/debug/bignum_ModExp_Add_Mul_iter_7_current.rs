use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{
}

proof fn lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{
}

proof fn lemma_str2int_append(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c))
    ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })
{
    let extended = s.push(c);
    assert(extended.len() == s.len() + 1);
    assert(extended.subrange(0, extended.len() as int - 1) =~= s);
}

proof fn lemma_valid_bit_string_push(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c))
{
    let extended = s.push(c);
    assert(forall |i: int| 0 <= i && i < s.len() as int ==> extended.index(i) == s.index(i));
    assert(extended.index(s.len() as int) == c);
}

proof fn lemma_reverse_valid_bit_string(s: Seq<char>)
    requires ValidBitString(s)
    ensures ValidBitString(s.reverse())
{
}

proof fn lemma_str2int_prepend_zero(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0, s.index(0) == '0'
    ensures Str2Int(s) == Str2Int(s.subrange(1, s.len() as int))
{
    if s.len() == 1 {
        assert(s =~= seq!['0']);
        assert(s.subrange(1, s.len() as int) =~= Seq::<char>::empty());
    } else {
        assert(s.subrange(0, s.len() as int - 1) =~= seq!['0'].add(s.subrange(1, s.len() as int - 1)));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<char>::new();
    let mut carry = 0u32;
    let mut i1 = s1.len();
    let mut i2 = s2.len();
    
    while i1 > 0 || i2 > 0 || carry > 0
        invariant
            carry <= 1,
            i1 <= s1.len(),
            i2 <= s2.len(),
            ValidBitString(result@),
            ValidBitString(s1@),
            ValidBitString(s2@)
    {
        let bit1 = if i1 > 0 {
            i1 -= 1;
            if s1[i1] == '1' { 1u32 } else { 0u32 }
        } else { 0u32 };
        
        let bit2 = if i2 > 0 {
            i2 -= 1;
            if s2[i2] == '1' { 1u32 } else { 0u32 }
        } else { 0u32 };
        
        let sum = bit1 + bit2 + carry;
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;
        
        result.push(result_bit);
        
        proof {
            assert(result_bit == '0' || result_bit == '1');
            lemma_valid_bit_string_push(result@.subrange(0, result@.len() as int - 1), result_bit);
        }
    }
    
    result.reverse();
    
    proof {
        lemma_reverse_valid_bit_string(result@);
    }
    
    if result.len() == 0 {
        result.push('0');
        proof {
            lemma_str2int_single_zero();
        }
    } else if result.len() > 1 && result[0] == '0' {
        while result.len() > 1 && result[0] == '0'
            invariant
                result.len() > 0,
                ValidBitString(result@),
                result.len() == 1 ==> result[0] != '0'
        {
            result.remove(0);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}