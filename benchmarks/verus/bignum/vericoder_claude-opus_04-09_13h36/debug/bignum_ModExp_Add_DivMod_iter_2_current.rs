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
    ensures Str2Int(s.push(bit)) == 2 * Str2Int(s) + if bit == '1' { 1 } else { 0 }
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

proof fn lemma_add_with_carry(s1: Seq<char>, s2: Seq<char>, result: Seq<char>, 
                              d1: char, d2: char, carry: u8, sum_bit: char, new_carry: u8)
    requires ValidBitString(s1),
             ValidBitString(s2),
             ValidBitString(result),
             d1 == '0' || d1 == '1',
             d2 == '0' || d2 == '1',
             carry == 0 || carry == 1,
             sum_bit == '0' || sum_bit == '1',
             new_carry == 0 || new_carry == 1,
             ({
                 let v1 = if d1 == '1' { 1u8 } else { 0u8 };
                 let v2 = if d2 == '1' { 1u8 } else { 0u8 };
                 let sum = v1 + v2 + carry;
                 (sum % 2 == if sum_bit == '1' { 1 } else { 0}) &&
                 (new_carry == sum / 2)
             })
    ensures Str2Int(result.push(sum_bit)) + (new_carry as nat) * Exp_int(2, result.len() + 1) ==
            Str2Int(s1.push(d1)) + Str2Int(s2.push(d2)) + (carry as nat) *
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{}

proof fn lemma_str2int_append_bit(s: Seq<char>, bit: char)
    requires ValidBitString(s),
             bit == '0' || bit == '1'
    ensures Str2Int(s.push(bit)) == 2 * Str2Int(s) + if bit == '1' { 1 } else { 0 }
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

proof fn lemma_add_with_carry(s1: Seq<char>, s2: Seq<char>, result: Seq<char>, 
                              d1: char, d2: char, carry: u8, sum_bit: char, new_carry: u8)
    requires ValidBitString(s1),
             ValidBitString(s2),
             ValidBitString(result),
             d1 == '0' || d1 == '1',
             d2 == '0' || d2 == '1',
             carry == 0 || carry == 1,
             sum_bit == '0' || sum_bit == '1',
             new_carry == 0 || new_carry == 1,
             ({
                 let v1 = if d1 == '1' { 1u8 } else { 0u8 };
                 let v2 = if d2 == '1' { 1u8 } else { 0u8 };
                 let sum = v1 + v2 + carry;
                 (sum % 2 == if sum_bit == '1' { 1 } else { 0}) &&
                 (new_carry == sum / 2)
             })
    ensures Str2Int(result.push(sum_bit)) + (new_carry as nat) * Exp_int(2, result.len() + 1) ==
            Str2Int(s1.push(d1)) + Str2Int(s2.push(d2)) + (carry as nat) *
// </vc-code>

fn main() {}
}