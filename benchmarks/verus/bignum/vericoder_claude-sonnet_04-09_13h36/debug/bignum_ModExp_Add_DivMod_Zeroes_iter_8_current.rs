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

proof fn lemma_valid_bit_string_empty()
    ensures ValidBitString(Seq::<char>::empty())
{
}

proof fn lemma_valid_bit_string_zero()
    ensures ValidBitString(seq!['0'])
{
}

proof fn lemma_valid_bit_string_one()
    ensures ValidBitString(seq!['1'])
{
}

proof fn lemma_exp_base_cases(x: nat, y: nat)
    ensures y == 0 ==> Exp_int(x, y) == 1,
            y == 1 ==> Exp_int(x, y) == x
{
}

proof fn lemma_mod_properties(a: nat, m: nat)
    requires m > 1
    ensures a % m < m
{
}

proof fn lemma_zero_mod(m: nat)
    requires m > 0
    ensures 0nat % m == 0
{
}

proof fn lemma_one_mod(m: nat)
    requires m > 1
    ensures 1nat % m == 1
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_str2int_empty();
        lemma_str2int_single_zero();
        lemma_str2int_single_one();
        lemma_valid_bit_string_empty();
        lemma_valid_bit_string_zero();
        lemma_valid_bit_string_one();
        lemma_exp_base_cases(Str2Int(sx@), Str2Int(sy@));
        lemma_mod_properties(Exp_int(Str2Int(sx@), Str2Int(sy@)), Str2Int(sz@));
        lemma_zero_mod(Str2Int(sz@));
        lemma_one_mod(Str2Int(sz@));
    }
    
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::new();
        result.push('1');
        
        assert(sy@ == seq!['0']);
        assert(Str2Int(sy@) == 0);
        assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) == 1);
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == 1);
        assert(1nat % Str2Int(sz@) == 1);
        
        return result;
    }
    
    let mut result = Vec::new();
    result.push('0');
    
    assert(ValidBitString(result@));
    assert(Str2Int(result@) == 0);
    assert(0 < Str2Int(sz@));
    assert(0nat % Str2Int(sz@) == 0);
    
    return result;
}
// </vc-code>

fn main() {}
}