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

spec fn partial_sum(s1: Seq<char>, s2: Seq<char>, i: nat) -> nat {
    let mut sum = 0nat;
    let mut j = 0;
    while j < i
        invariant 0 <= j <= i
        decreases i - j
    {
        let bit1 = if j < s1.len() { bit_value(s1[s1.len() - 1 - j]) } else { 0nat };
        let bit2 = if j < s2.len() { bit_value(s2[s2.len() - 1 - j]) } else { 0nat };
        sum = sum + (bit1 + bit2) * Exp_int(2, j);
        j = j + 1;
    }
    sum
}

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
{}

spec fn result_represents(result: Seq<char>, s1: Seq<char>, s2: Seq<char>, pos: nat, carry_in: nat) -> bool {
    if result.len() == 0 {
        pos == 0 && carry_in == 0
    } else {
        let expected = partial_sum(s1, s2, pos) + carry_in;
        Str2Int(result) == expected
    }
}

proof fn lemma_exp_powers(n: nat)
    ensures Exp_int(2, n + 1) == 2 * Exp_int(2, n)
    decreases n
{
    if n == 0 {
        assert(Exp_int(2, 1) == 2 * Exp_int(2, 0));
    } else {
        lemma_exp_powers((n - 1) as nat);
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
        }
        
        i += 1;
    }
    
    if result.len() == 0 {
        result.push('0');
        proof {
            assert(ValidBitString(seq!['0']));
            assert(Str2Int(seq!['0']) == 0);
            assert(Str2Int(s1@) + Str2Int(s2@) == 0);
        }
    } else {
        proof {
            assert(carry == 0);
            assert(i >= max_len);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}