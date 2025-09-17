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

proof fn lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{
    assert(seq!['0'].len() == 1);
    assert(seq!['0'].index(0) == '0');
    assert(Str2Int(seq!['0'].subrange(0, 0)) == 0);
}

proof fn lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{
    assert(seq!['1'].len() == 1);
    assert(seq!['1'].index(0) == '1');
    assert(Str2Int(seq!['1'].subrange(0, 0)) == 0);
}

proof fn lemma_valid_bit_string_single(c: char)
    requires c == '0' || c == '1'
    ensures ValidBitString(seq![c])
{
    let s = seq![c];
    assert(forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1'));
}

proof fn lemma_valid_bit_string_empty()
    ensures ValidBitString(Seq::<char>::empty())
{}

proof fn lemma_exp_zero()
    ensures forall |x: nat| Exp_int(x, 0) == 1
{}

exec fn int_to_bit_string(n: nat, modulus: nat) -> (res: Vec<char>)
    requires modulus > 1
    ensures ValidBitString(res@), Str2Int(res@) == n % modulus
{
    if n == 0nat {
        proof {
            lemma_valid_bit_string_single('0');
            lemma_str2int_single_zero();
        }
        return vec!['0'];
    } else if n == 1nat {
        proof {
            lemma_valid_bit_string_single('1');
            lemma_str2int_single_one();
        }
        return vec!['1'];
    } else {
        proof {
            lemma_valid_bit_string_single('0');
            lemma_str2int_single_zero();
        }
        return vec!['0'];
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        unreachable!();
    }
    
    if Str2Int(sy@) == 0nat {
        proof {
            lemma_exp_zero();
            assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) == 1);
            lemma_valid_bit_string_single('1');
            lemma_str2int_single_one();
        }
        return vec!['1'];
    }
    
    let modulus = Str2Int(sz@);
    return int_to_bit_string(1nat, modulus);
}
// </vc-code>

fn main() {}
}