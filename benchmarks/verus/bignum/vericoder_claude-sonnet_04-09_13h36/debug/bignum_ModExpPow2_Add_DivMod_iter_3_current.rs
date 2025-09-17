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
lemma fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

lemma fn lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{
}

lemma fn lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{
}

lemma fn lemma_str2int_push_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures ValidBitString(s.push('0'))
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
{
    let s_new = s.push('0');
    if s.len() == 0 {
        assert(s_new =~= seq!['0']);
        assert(Str2Int(s_new) == 0);
        assert(2 * Str2Int(s) == 2 * 0);
    } else {
        assert(s_new.len() > 0);
        assert(s_new.subrange(0, s_new.len() as int - 1) =~= s);
        assert(s_new.index(s_new.len() as int - 1) == '0');
        assert(Str2Int(s_new) == 2 * Str2Int(s_new.subrange(0, s_new.len() as int - 1)) + 0);
        assert(Str2Int(s_new) == 2 * Str2Int(s));
    }
}

lemma fn lemma_str2int_push_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures ValidBitString(s.push('1'))
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
    let s_new = s.push('1');
    if s.len() == 0 {
        assert(s_new =~= seq!['1']);
        assert(Str2Int(s_new) == 1);
        assert(2 * Str2Int(s) + 1 == 2 * 0 + 1);
    } else {
        assert(s_new.len() > 0);
        assert(s_new.subrange(0, s_new.len() as int - 1) =~= s);
        assert(s_new.index(s_new.len() as int - 1) == '1');
        assert(Str2Int(s_new) == 2 * Str2Int(s_new.subrange(0, s_new.len() as int - 1)) + 1);
        assert(Str2Int(s_new) == 2 * Str2Int(s) + 1);
    }
}

lemma fn lemma_valid_bit_string_push(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c))
{
    let s_new = s.push(c);
    assert forall |i: int| 0 <= i && i < s_new.len() as int implies (s_new.index(i) == '0' || s_new.index(i) == '1') by {
        if i < s.len() as int {
            assert(s_new.index(i) == s.index(i));
            assert(s.index(i) == '0' || s.index(i) == '1');
        } else {
            assert(i == s.len() as int);
            assert(s_new.index(i) == c);
        }
    }
}

exec fn char_to_digit(c: char) -> (res: u8)
    requires c == '0' || c == '1'
    ensures res == 0 || res == 1
    ensures res == 0 <==> c == '0'
    ensures res == 1 <==> c == '1'
{
    if c == '0' { 0 } else { 1 }
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
    let mut carry: u8 = 0;
    let mut i1 = s1.len();
    let mut i2 = s2.len();
    
    while i1 > 0 || i2 > 0 || carry > 0
        invariant
            ValidBitString(result@),
            carry == 0 || carry == 1,
            i1 <= s1.len(),
            i2 <= s2.len(),
            ValidBitString(s1@),
            ValidBitString(s2@)
    {
        let d1: u8 = if i1 > 0 {
            i1 = i1 - 1;
            char_to_digit(s1[i1])
        } else { 0 };
        
        let d2: u8 = if i2 > 0 {
            i2 = i2 - 1;
            char_to_digit(s2[i2])
        } else { 0 };
        
        let sum = d1 + d2 + carry;
        let digit = sum % 2;
        carry = sum / 2;
        
        let digit_char = if digit == 0 { '0' } else { '1' };
        result.push(digit_char);
        
        proof {
            lemma_valid_bit_string_push(result@.drop_last(), digit_char);
        }
    }
    
    result.reverse();
    
    // Remove leading zeros if any (but keep at least one digit)
    while result.len() > 1 && result[0] == '0'
        invariant
            result.len() > 0,
            ValidBitString(result@)
    {
        result.remove(0);
    }
    
    // If result is empty, add '0'
    if result.len() == 0 {
        result.push('0');
        proof {
            lemma_valid_bit_string_push(Seq::<char>::empty(), '0');
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}