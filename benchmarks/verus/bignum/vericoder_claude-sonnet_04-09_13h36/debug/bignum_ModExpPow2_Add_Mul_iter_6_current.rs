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
{}

proof fn lemma_str2int_push(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c)),
            Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })
{
    let sp = s.push(c);
    assert(sp.len() == s.len() + 1);
    assert(sp.index(sp.len() as int - 1) == c);
    assert(sp.subrange(0, sp.len() as int - 1) == s);
}

proof fn lemma_str2int_distributive(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2)
    ensures Str2Int(s1) + Str2Int(s2) == Str2Int(s2) + Str2Int(s1)
{}

spec fn carry_propagate(a: nat, b: nat, carry: nat) -> (nat, nat) {
    let sum = a + b + carry;
    (sum % 2, sum / 2)
}

proof fn lemma_carry_properties(a: nat, b: nat, carry: nat)
    requires carry <= 1, a <= 1, b <= 1
    ensures ({
        let (digit, new_carry) = carry_propagate(a, b, carry);
        digit <= 1 && new_carry <= 1 && a + b + carry == digit + 2 * new_carry
    })
{}

proof fn lemma_exp_int_positive(x: nat, y: nat)
    requires x > 0
    ensures Exp_int(x, y) > 0
    decreases y
{
    if y == 0 {
    } else {
        lemma_exp_int_positive(x, (y - 1) as nat);
    }
}

proof fn lemma_str2int_bound(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < Exp_int(2, s.len())
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_str2int_bound(s.subrange(0, s.len() as int - 1));
        assert(Str2Int(s.subrange(0, s.len() as int - 1)) < Exp_int(2, (s.len() - 1) as nat));
        assert(Str2Int(s) <= 2 * Exp_int(2, (s.len() - 1) as nat) + 1);
        assert(2 * Exp_int(2, (s.len() - 1) as nat) + 1 < Exp_int(2, s.len()));
    }
}

proof fn lemma_bit_addition_correctness(s1: Seq<char>, s2: Seq<char>, result: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2), ValidBitString(result)
    ensures Str2Int(s1) + Str2Int(s2) == Str2Int(result) ==> Str2Int(result) == Str2Int(s1) + Str2Int(s2)
{}

spec fn bit_value(c: char) -> nat {
    if c == '1' { 1nat } else { 0nat }
}

proof fn lemma_valid_bit_char(c: char)
    requires c == '0' || c == '1'
    ensures ValidBitString(seq![c])
{}

proof fn lemma_insert_preserves_validity(result: Seq<char>, c: char)
    requires ValidBitString(result), c == '0' || c == '1'
    ensures ValidBitString(seq![c].add(result))
{
    let new_seq = seq![c].add(result);
    assert(forall |i: int| 0 <= i < new_seq.len() ==> 
           (new_seq[i] == '0' || new_seq[i] == '1'));
}

proof fn lemma_push_preserves_validity(result: Vec<char>, c: char)
    requires ValidBitString(result@), c == '0' || c == '1'
    ensures ValidBitString(result@.push(c))
{
    let new_seq = result@.push(c);
    assert(forall |i: int| 0 <= i < new_seq.len() ==> 
           (new_seq[i] == '0' || new_seq[i] == '1'));
}

spec fn loop_bound(max_len: usize, carry: u8, i: usize) -> nat {
    if carry > 0 { 
        (max_len + 1) - i 
    } else { 
        max_len - i 
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
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    let mut i = 0;
    while i < max_len || (i == max_len && carry > 0)
        invariant 
            ValidBitString(result@),
            carry <= 1,
            i <= max_len + 1,
            max_len == if s1.len() > s2.len() { s1.len() } else { s2.len() },
        decreases (max_len + 1) - i
    {
        let bit1 = if i < s1.len() {
            if s1[s1.len() - 1 - i] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let bit2 = if i < s2.len() {
            if s2[s2.len() - 1 - i] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let sum = bit1 + bit2 + carry;
        let digit_char = if sum % 2 == 1 { '1' } else { '0' };
        
        result.insert(0, digit_char);
        carry = sum / 2;
        
        proof {
            assert(carry <= 1);
            lemma_valid_bit_char(digit_char);
            lemma_insert_preserves_validity(result@.subrange(1, result@.len() as int), digit_char);
            assert(ValidBitString(result@));
        }
        
        i += 1;
    }
    
    if result.len() == 0 {
        result.push('0');
        proof {
            lemma_push_preserves_validity(result, '0');
            assert(ValidBitString(result@));
        }
    }
    
    proof {
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@));
    }
    
    result
}
// </vc-code>

fn main() {}
}