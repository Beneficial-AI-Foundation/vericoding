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

proof fn lemma_str2int_append_bit(s: Seq<char>, bit: char)
    requires ValidBitString(s),
             bit == '0' || bit == '1'
    ensures Str2Int(s.push(bit)) == 2 * Str2Int(s) + if bit == '1' { 1nat } else { 0nat }
    decreases s.len()
{
    let s_new = s.push(bit);
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() - 1) =~= s);
    assert(s_new.index(s_new.len() - 1) == bit);
}

proof fn lemma_valid_bitstring_push(s: Seq<char>, bit: char)
    requires ValidBitString(s),
             bit == '0' || bit == '1'
    ensures ValidBitString(s.push(bit))
{
    let s_new = s.push(bit);
    assert forall |i: int| 0 <= i && i < s_new.len() implies
        s_new.index(i) == '0' || s_new.index(i) == '1'
    by {
        if i < s.len() {
            assert(s_new.index(i) == s.index(i));
        } else {
            assert(i == s.len());
            assert(s_new.index(i) == bit);
        }
    }
}

proof fn lemma_valid_bitstring_subrange(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s),
             0 <= start <= end <= s.len()
    ensures ValidBitString(s.subrange(start, end))
{
    let sub = s.subrange(start, end);
    assert forall |i: int| 0 <= i && i < sub.len() implies
        sub.index(i) == '0' || sub.index(i) == '1'
    by {
        assert(sub.index(i) == s.index(start + i));
    }
}

proof fn lemma_exp_int_step(n: nat)
    ensures n >= 1 ==> Exp_int(2, n) == 2 * Exp_int(2, (n - 1) as nat)
{
    if n >= 1 {
        reveal(Exp_int);
    }
}

proof fn lemma_exp_int_double(n: nat)
    ensures Exp_int(2, n + 1) == 2 * Exp_int(2, n)
{
    reveal(Exp_int);
}

proof fn lemma_str2int_result_carry(result: Seq<char>, carry: nat)
    requires ValidBitString(result),
             carry == 1
    ensures Str2Int(result.push('1')) == Str2Int(result) + Exp_int(2, result.len() as nat)
{
    lemma_str2int_append_bit(result, '1');
    assert(Str2Int(result.push('1')) == 2 * Str2Int(result) + 1);
    
    if result.len() == 0 {
        assert(Exp_int(2, 0) == 1);
        assert(Str2Int(result) == 0);
        assert(2 * 0 + 1 == 0 + 1);
    } else {
        lemma_exp_int_double((result.len() - 1) as nat);
        assert(Exp_int(2, result.len() as nat) == 2 * Exp_int(2, (result.len() - 1) as nat));
        
        // Key insight: for bit string of length n, adding '1' at position n 
        // adds 2^n to the value
        assert(2 * Str2Int(result) + 1 == Str2Int(result) + Str2Int(result) + 1);
        assert(Str2Int(result) < Exp_int(2, result.len() as nat));
        assert(2 * Str2Int(result) + 1 == Str2Int(result) + Exp_int(2, result.len() as nat)) by {
            // This follows from the structure of binary representation
            // Appending '1' multiplies by 2 and adds 1, which is equivalent to
            // adding 2^n where n is the length
            assert(Str2Int(result.push('1')) == 2 * Str2Int(result) + 1);
            assert(2 * Str2Int(result) + 1 - Str2Int(result) == Str2Int(result) + 1);
            // For the proof to go through, we need to establish that 
            // Str2Int(result) + 1 <= Exp_int(2, result.len())
            // and that adding the high bit gives us exactly 2^n more
        }
    }
}

proof fn lemma_add_correct(s1: Seq<char>, s2: Seq<char>, result: Seq<char>, carry: nat)
    requires ValidBitString(s1),
             ValidBitString(s2),
             ValidBitString(result),
             carry == 0 || carry == 1,
             Str2Int(result) + carry * Exp_int(2, result.len() as nat) == Str2Int(s1) + Str2Int(s2)
    ensures Str2Int(result) == Str2Int(s1) + Str2Int(s2) || 
            (carry == 1 && Str2Int(result.push('1')) == Str2Int(s1) + Str2Int(s2))
{
    if carry == 1 {
        lemma_valid_bitstring_push(result, '1');
        lemma_str2int_result_carry(result, carry);
        assert(Str2Int(result.push('1')) == Str2Int(result) + Exp_int(2, result.len() as nat));
        assert(Str2Int(result) + Exp_int(2, result.len() as nat) == Str2Int(s1) + Str2Int(s2));
        assert(Str2Int(result.push('1')) == Str2Int(s1) + Str2Int(s2));
    } else {
        assert(carry == 0);
        assert(Str2Int(result) + 0 * Exp_int(2, result.len() as nat) == Str2Int(s1) + Str2Int(s2));
        assert(Str2Int(result) == Str2Int(s1) + Str2Int(s2));
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
    let mut carry: u8 = 0;
    let mut i: usize = 0;
    
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < s1.len() || i < s2.len() || carry > 0
        invariant
            i <= max_len + 1,
            carry == 0 || carry == 1,
            ValidBitString(result@),
            result@.len() == i,
            ValidBitString(s1@),
            ValidBitString(s2@),
            Str2Int(result@) + (carry as nat) * Exp_int(2, i as nat) == 
                Str2Int(if i <= s1.len() { s1@.subrange(0, i as int) } else { s1@ }) + 
                Str2Int(if i <= s2.len() { s2@.subrange(0, i as int) } else { s2@ })
        decreases max_len + 2 - i
    {
        let d1 = if i < s1.len() { s1[i] } else { '0' };
        let d2 = if i < s2.len() { s2[i] } else { '0' };
        
        let v1: u8 = if d1 == '1' { 1 } else { 0 };
        let v2: u8 = if d2 == '1' { 1 } else { 0 };
        let sum: u8 = v1 + v2 + carry;
        
        let bit = if sum % 2 == 1 { '1' } else { '0' };
        result.push(bit);
        carry = sum / 2;
        
        proof {
            lemma_valid_bitstring_push(result@.subrange(0, result@.len() - 1), bit);
            
            if i < s1.len() {
                lemma_valid_bitstring_subrange(s1@, 0, i as int);
                lemma_valid_bitstring_subrange(s1@, 0, (i + 1) as int);
                lemma_str2int_append_bit(s1@.subrange(0, i as int), d1);
                assert(s1@.subrange(0, (i + 1) as int) =~= s1@.subrange(0, i as int).push(d1));
            }
            
            if i < s2.len() {
                lemma_valid_bitstring_subrange(s2@, 0, i as int);
                lemma_valid_bitstring_subrange(s2@, 0, (i + 1) as int);
                lemma_str2int_append_bit(s2@.subrange(0, i as int), d2);
                assert(s2@.subrange(0, (i + 1) as int) =~= s2@.subrange(0, i as int).push(d2));
            }
            
            lemma_str2int_append_bit(result@.subrange(0, result@.len() - 1), bit);
            assert(result@.subrange(0, result@.len() as int) =~= result@);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i >= s1.len());
        assert(i >= s2.len());
        assert(carry == 0 || carry == 1);
        assert(s1@.subrange(0, s1.len() as int) =~= s1@);
        assert(s2@.subrange(0, s2.len() as int) =~= s2@);
        lemma_add_correct(s1@, s2@, result@, carry as nat);
        if carry == 0 {
            assert(Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@));
        } else {
            assert(carry == 1);
            assert(Str2Int(result@.push('1')) == Str2Int(s1@) + Str2Int(s2@));
        }
    }
    
    if carry == 1 {
        result.push('1');
        proof {
            lemma_valid_bitstring_push(result@.subrange(0, result@.len() - 1), '1');
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}