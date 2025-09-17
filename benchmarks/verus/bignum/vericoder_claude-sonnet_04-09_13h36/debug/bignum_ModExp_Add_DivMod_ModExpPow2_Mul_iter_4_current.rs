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
proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push('0') == seq!['0']);
        assert(Str2Int(s.push('0')) == 0);
        assert(Str2Int(s) == 0);
    } else {
        let s_extended = s.push('0');
        assert(s_extended.len() == s.len() + 1);
        assert(s_extended.index(s_extended.len() as int - 1) == '0');
        assert(s_extended.subrange(0, s_extended.len() as int - 1) == s);
        assert(Str2Int(s_extended) == 2 * Str2Int(s) + 0);
    }
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push('1') == seq!['1']);
        assert(Str2Int(s.push('1')) == 1);
        assert(Str2Int(s) == 0);
    } else {
        let s_extended = s.push('1');
        assert(s_extended.len() == s.len() + 1);
        assert(s_extended.index(s_extended.len() as int - 1) == '1');
        assert(s_extended.subrange(0, s_extended.len() as int - 1) == s);
        assert(Str2Int(s_extended) == 2 * Str2Int(s) + 1);
    }
}

proof fn lemma_valid_bit_string_push(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c))
{
    let s_new = s.push(c);
    assert forall |i: int| 0 <= i && i < s_new.len() as int implies 
        (s_new.index(i) == '0' || s_new.index(i) == '1') by {
        if i < s.len() as int {
            assert(s_new.index(i) == s.index(i));
        } else {
            assert(i == s.len() as int);
            assert(s_new.index(i) == c);
        }
    };
}

proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_reverse_valid_bit_string(s: Seq<char>)
    requires ValidBitString(s)
    ensures ValidBitString(s.reverse())
{
    assert forall |i: int| 0 <= i && i < s.reverse().len() as int implies 
        (s.reverse().index(i) == '0' || s.reverse().index(i) == '1') by {
        assert(s.reverse().index(i) == s.index(s.len() as int - 1 - i));
    };
}

proof fn lemma_manual_reverse_preserves_valid_bit_string(original: Seq<char>, reversed: Seq<char>)
    requires 
        ValidBitString(original),
        reversed.len() == original.len(),
        forall |i: int| 0 <= i && i < original.len() as int ==> 
            reversed.index(i) == original.index(original.len() as int - 1 - i)
    ensures ValidBitString(reversed)
{
    assert forall |i: int| 0 <= i && i < reversed.len() as int implies 
        (reversed.index(i) == '0' || reversed.index(i) == '1') by {
        let orig_idx = original.len() as int - 1 - i;
        assert(0 <= orig_idx && orig_idx < original.len() as int);
        assert(original.index(orig_idx) == '0' || original.index(orig_idx) == '1');
        assert(reversed.index(i) == original.index(orig_idx));
    };
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
    
    if s1.len() == 0 && s2.len() == 0 {
        result.push('0');
        proof {
            lemma_valid_bit_string_push(Seq::<char>::empty(), '0');
            assert(Str2Int(result@) == 0);
            assert(Str2Int(s1@) + Str2Int(s2@) == 0);
        }
        return result;
    }
    
    let mut carry = 0u8;
    let mut i1 = s1.len();
    let mut i2 = s2.len();
    
    while i1 > 0 || i2 > 0 || carry > 0
        invariant 
            ValidBitString(result@),
            carry <= 2,
            i1 <= s1.len(),
            i2 <= s2.len()
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
        
        proof {
            lemma_valid_bit_string_push(result@.subrange(0, result@.len() as int - 1), result_bit);
        }
    }
    
    if result.len() == 0 {
        result.push('0');
        proof {
            lemma_valid_bit_string_push(Seq::<char>::empty(), '0');
        }
    }
    
    // Store the original sequence before reversal for proof purposes
    let original_seq = result@;
    
    // Manually reverse the result vector
    let len = result.len();
    let mut i = 0;
    while i < len / 2
        invariant
            i <= len / 2,
            len == result.len(),
            ValidBitString(result@)
    {
        let temp = result[i];
        result.set(i, result[len - 1 - i]);
        result.set(len - 1 - i, temp);
        i += 1;
    }
    
    proof {
        lemma_manual_reverse_preserves_valid_bit_string(original_seq, result@);
        assert(Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@));
    }
    
    result
}
// </vc-code>

fn main() {}
}