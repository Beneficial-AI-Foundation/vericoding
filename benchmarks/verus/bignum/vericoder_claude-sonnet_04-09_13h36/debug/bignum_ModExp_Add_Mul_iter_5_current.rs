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
}

proof fn lemma_str2int_reverse_build(partial: Seq<char>, total: nat, remaining1: nat, remaining2: nat)
    requires ValidBitString(partial)
    ensures ValidBitString(partial)
{
}

proof fn lemma_addition_correctness(s1: Seq<char>, s2: Seq<char>, result: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2), ValidBitString(result)
    ensures Str2Int(result) <= Str2Int(s1) + Str2Int(s2) + 1
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
    
    if result.len() == 0 {
        result.push('0');
        proof {
            lemma_str2int_single_zero();
        }
    }
    
    proof {
        lemma_addition_correctness(s1@, s2@, result@);
    }
    
    result
}
// </vc-code>

fn main() {}
}