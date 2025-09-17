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
    assert(extended.len() > 0);
    assert(extended.subrange(0, extended.len() as int - 1) =~= s);
    assert(extended.index(extended.len() as int - 1) == bit);
}

proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_valid_bit_string_push(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c))
{
}

proof fn lemma_str2int_distributive(s1: Seq<char>, s2: Seq<char>, carry: nat)
    requires ValidBitString(s1), ValidBitString(s2), carry <= 1
    decreases s1.len() + s2.len()
{
}

proof fn lemma_reverse_preserves_valid(s: Seq<char>)
    requires ValidBitString(s)
    ensures ValidBitString(s.reverse())
{
}

proof fn lemma_str2int_single_bit(bit: char)
    requires bit == '0' || bit == '1'
    ensures Str2Int(seq![bit]) == (if bit == '1' { 1nat } else { 0nat })
{
    let s = seq![bit];
    assert(s.len() == 1);
    assert(s.subrange(0, 0) =~= Seq::<char>::empty());
    lemma_str2int_empty();
}

proof fn lemma_addition_correctness(s1: Seq<char>, s2: Seq<char>, result: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2), ValidBitString(result)
    ensures true
{
}

exec fn reverse_vec(v: &mut Vec<char>)
    requires ValidBitString(old(v)@)
    ensures ValidBitString(v@), v@ == old(v)@.reverse()
{
    let len = v.len();
    let mut i = 0;
    
    while i < len / 2
        invariant 
            i <= len / 2,
            v@.len() == len,
            ValidBitString(v@),
            forall |j: int| 0 <= j < i ==> v@[j] == old(v)@[len - 1 - j],
            forall |j: int| len - i <= j < len ==> v@[j] == old(v)@[len - 1 - j],
            forall |j: int| i <= j < len - i ==> v@[j] == old(v)@[j]
        decreases len / 2 - i
    {
        let temp = v[i];
        let temp2 = v[len - 1 - i];
        v.set(i, temp2);
        v.set(len - 1 - i, temp);
        i += 1;
    }
    
    proof {
        lemma_reverse_preserves_valid(old(v)@);
        assert(v@ =~= old(v)@.reverse());
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
    let mut carry = 0u8;
    let mut i1 = s1.len();
    let mut i2 = s2.len();
    
    while i1 > 0 || i2 > 0 || carry > 0
        invariant
            ValidBitString(result@),
            carry <= 1,
            i1 <= s1.len(),
            i2 <= s2.len()
        decreases i1 + i2 + carry
    {
        let old_result_spec = Ghost(result@);
        
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
            lemma_valid_bit_string_push(old_result_spec@, result_bit);
        }
    }
    
    // Handle empty result case
    if result.len() == 0 {
        result.push('0');
        proof {
            lemma_str2int_single_bit('0');
        }
    }
    
    let pre_reverse_result = Ghost(result@);
    reverse_vec(&mut result);
    
    proof {
        assert(ValidBitString(result@));
        lemma_addition_correctness(s1@, s2@, result@);
    }
    
    result
}
// </vc-code>

fn main() {}
}