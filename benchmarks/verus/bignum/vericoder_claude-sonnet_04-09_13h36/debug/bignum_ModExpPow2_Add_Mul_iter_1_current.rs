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
lemma lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{}

lemma lemma_str2int_push(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c))
    ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })
{
    let sp = s.push(c);
    assert(sp.len() == s.len() + 1);
    assert(sp.index(sp.len() as int - 1) == c);
    assert(sp.subrange(0, sp.len() as int - 1) == s);
}

lemma lemma_str2int_distributive(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2)
    ensures Str2Int(s1) + Str2Int(s2) == Str2Int(s2) + Str2Int(s1)
{}

spec fn carry_propagate(a: nat, b: nat, carry: nat) -> (nat, nat) {
    let sum = a + b + carry;
    (sum % 2, sum / 2)
}

lemma lemma_carry_properties(a: nat, b: nat, carry: nat)
    requires carry <= 1, a <= 1, b <= 1
    ensures {
        let (digit, new_carry) = carry_propagate(a, b, carry);
        digit <= 1 && new_carry <= 1 && a + b + carry == digit + 2 * new_carry
    }
{}

lemma lemma_exp_int_positive(x: nat, y: nat)
    requires x > 0
    ensures Exp_int(x, y) > 0
    decreases y
{
    if y == 0 {
    } else {
        lemma_exp_int_positive(x, (y - 1) as nat);
    }
}

lemma lemma_str2int_bound(s: Seq<char>)
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

spec fn bit_addition_spec(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
    recommends ValidBitString(s1), ValidBitString(s2)
{
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    let mut result: Seq<char> = Seq::empty();
    let mut carry = 0nat;
    let mut i = 0nat;
    
    while i <= max_len
        invariant ValidBitString(result)
    {
        let bit1 = if i < s1.len() { if s1@[s1.len() - 1 - i] == '1' { 1nat } else { 0nat } } else { 0nat };
        let bit2 = if i < s2.len() { if s2@[s2.len() - 1 - i] == '1' { 1nat } else { 0nat } } else { 0nat };
        let sum = bit1 + bit2 + carry;
        let digit_char = if sum % 2 == 1 { '1' } else { '0' };
        result = Seq::empty().push(digit_char) + result;
        carry = sum / 2;
        i = i + 1;
    }
    
    result
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
    while i <= max_len
        invariant 
            ValidBitString(result@),
            carry <= 1,
            i <= max_len + 1,
            max_len == if s1.len() > s2.len() { s1.len() } else { s2.len() },
    {
        let bit1 = if i < s1.len() {
            if s1[s1.len() - 1 - i] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let bit2 = if i < s2.len() {
            if s2[s2.len() - 1 - i] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let sum = bit1 + bit2 + carry;
        
        if sum == 0 && i == max_len {
            break;
        }
        
        let digit_char = if sum % 2 == 1 { '1' } else { '0' };
        result.insert(0, digit_char);
        
        carry = sum / 2;
        i += 1;
    }
    
    if result.is_empty() {
        result.push('0');
    }
    
    proof {
        assert(ValidBitString(result@));
    }
    
    result
}
// </vc-code>

fn main() {}
}