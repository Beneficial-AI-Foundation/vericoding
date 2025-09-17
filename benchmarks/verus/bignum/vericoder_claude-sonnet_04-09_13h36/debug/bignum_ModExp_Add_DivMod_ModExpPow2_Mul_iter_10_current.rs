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
    let s_extended = s.push('0');
    assert(s_extended.len() == s.len() + 1);
    assert(s_extended.index(s_extended.len() as int - 1) == '0');
    assert(s_extended.subrange(0, s_extended.len() as int - 1) == s);
    assert(Str2Int(s_extended) == 2 * Str2Int(s) + 0);
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
    decreases s.len()
{
    let s_extended = s.push('1');
    assert(s_extended.len() == s.len() + 1);
    assert(s_extended.index(s_extended.len() as int - 1) == '1');
    assert(s_extended.subrange(0, s_extended.len() as int - 1) == s);
    assert(Str2Int(s_extended) == 2 * Str2Int(s) + 1);
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

proof fn lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{
    let s = seq!['0'];
    assert(s.len() == 1);
    assert(s.index(0) == '0');
    assert(s.subrange(0, 0) == Seq::<char>::empty());
    assert(Str2Int(s.subrange(0, 0)) == 0);
    assert(Str2Int(s) == 2 * 0 + 0);
}

proof fn lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{
    let s = seq!['1'];
    assert(s.len() == 1);
    assert(s.index(0) == '1');
    assert(s.subrange(0, 0) == Seq::<char>::empty());
    assert(Str2Int(s.subrange(0, 0)) == 0);
    assert(Str2Int(s) == 2 * 0 + 1);
}

spec fn binary_add_value(s1: Seq<char>, s2: Seq<char>, result_reversed: Seq<char>) -> bool {
    ValidBitString(s1) && ValidBitString(s2) && ValidBitString(result_reversed) ==>
    Str2Int(result_reversed.reverse()) == Str2Int(s1) + Str2Int(s2)
}

proof fn lemma_reverse_preserves_valid_bit_string(s: Seq<char>)
    requires ValidBitString(s)
    ensures ValidBitString(s.reverse())
{
    assert forall |i: int| 0 <= i && i < s.reverse().len() as int implies 
        (s.reverse().index(i) == '0' || s.reverse().index(i) == '1') by {
        assert(s.reverse().index(i) == s.index(s.len() as int - 1 - i));
    };
}

proof fn lemma_manual_reverse_correct(v: Vec<char>, original: Seq<char>)
    requires 
        v@.len() == original.len(),
        forall |i: int| 0 <= i && i < original.len() as int ==> 
            v@.index(i) == original.index(original.len() as int - 1 - i),
        ValidBitString(original)
    ensures 
        ValidBitString(v@),
        v@ == original.reverse()
{
    lemma_reverse_preserves_valid_bit_string(original);
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    if s1.len() == 0 && s2.len() == 0 {
        let mut result = Vec::<char>::new();
        result.push('0');
        proof {
            lemma_str2int_single_zero();
            lemma_valid_bit_string_push(Seq::<char>::empty(), '0');
            lemma_str2int_empty();
        }
        return result;
    }

    let mut result = Vec::<char>::new();
    let mut carry = 0u8;
    let mut i1 = s1.len();
    let mut i2 = s2.len();
    
    // Keep track of the original sequences for the proof
    proof {
        let original_s1 = s1@;
        let original_s2 = s2@;
    }
    
    while i1 > 0 || i2 > 0 || carry > 0
        invariant 
            ValidBitString(result@),
            carry <= 1,
            i1 <= s1.len(),
            i2 <= s2.len()
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
        
        proof {
            lemma_valid_bit_string_push(result@.subrange(0, result@.len() as int - 1), result_bit);
        }
    }
    
    // Store the reversed result before manual reverse
    proof {
        let reversed_result = result@;
    }
    
    // Manual reverse
    let len = result.len();
    let mut i = 0;
    while i < len / 2
        invariant
            i <= len / 2,
            len == result.len(),
            ValidBitString(result@)
        decreases len / 2 - i
    {
        let temp = result[i];
        let other_temp = result[len - 1 - i];
        result.set(i, other_temp);
        result.set(len - 1 - i, temp);
        i += 1;
    }
    
    proof {
        let original_s1 = s1@;
        let original_s2 = s2@;
        
        // For simple cases, establish the correctness
        if original_s1.len() == 0 {
            lemma_str2int_empty();
            assert(Str2Int(original_s1) == 0);
        }
        if original_s2.len() == 0 {
            lemma_str2int_empty();
            assert(Str2Int(original_s2) == 0);
        }
        if original_s1.len() == 1 && original_s1.index(0) == '0' {
            lemma_str2int_single_zero();
        }
        if original_s1.len() == 1 && original_s1.index(0) == '1' {
            lemma_str2int_single_one();
        }
        if original_s2.len() == 1 && original_s2.index(0) == '0' {
            lemma_str2int_single_zero();
        }
        if original_s2.len() == 1 && original_s2.index(0) == '1' {
            lemma_str2int_single_one();
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}