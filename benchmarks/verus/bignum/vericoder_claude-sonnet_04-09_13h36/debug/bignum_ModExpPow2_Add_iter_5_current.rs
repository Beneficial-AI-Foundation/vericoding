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
proof fn lemma_str2int_append_bit(s: Seq<char>, bit: char)
    requires ValidBitString(s), bit == '0' || bit == '1'
    ensures ValidBitString(s.push(bit)),
            Str2Int(s.push(bit)) == 2 * Str2Int(s) + (if bit == '1' { 1nat } else { 0nat })
{
    let extended = s.push(bit);
    assert(extended.len() == s.len() + 1);
    assert(extended.index(extended.len() as int - 1) == bit);
    assert(extended.subrange(0, extended.len() as int - 1) =~= s);
}

proof fn lemma_str2int_empty()
    ensures ValidBitString(seq![]), Str2Int(seq![]) == 0
{
}

proof fn lemma_valid_bit_string_slice(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s), 0 <= start <= end <= s.len()
    ensures ValidBitString(s.subrange(start, end))
{
}

proof fn lemma_exp_positive(x: nat, y: nat)
    requires x > 0
    ensures Exp_int(x, y) > 0
    decreases y
{
    if y == 0 {
    } else {
        lemma_exp_positive(x, (y - 1) as nat);
    }
}

proof fn lemma_str2int_split(s: Seq<char>, i: int)
    requires ValidBitString(s), 0 <= i < s.len()
    ensures Str2Int(s) == Str2Int(s.subrange(0, i)) * Exp_int(2, (s.len() - i) as nat) + Str2Int(s.subrange(i, s.len() as int))
    decreases s.len()
{
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
    let mut carry = 0u8;
    let mut i1 = s1.len();
    let mut i2 = s2.len();
    
    while i1 > 0 || i2 > 0 || carry > 0
        invariant
            carry <= 2,
            i1 <= s1.len(),
            i2 <= s2.len(),
            ValidBitString(result@.reverse())
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
    }
    
    result.reverse();
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}