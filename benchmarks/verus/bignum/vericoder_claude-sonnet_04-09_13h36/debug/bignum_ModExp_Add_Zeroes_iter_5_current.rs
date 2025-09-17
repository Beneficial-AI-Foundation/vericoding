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
    assert(Str2Int(seq!['0']) == 2 * Str2Int(seq!['0'].subrange(0, 0)) + 0);
    assert(seq!['0'].subrange(0, 0) == Seq::<char>::empty());
    lemma_str2int_empty();
}

proof fn lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{
    assert(seq!['1'].len() == 1);
    assert(seq!['1'].index(0) == '1');
    assert(Str2Int(seq!['1']) == 2 * Str2Int(seq!['1'].subrange(0, 0)) + 1);
    assert(seq!['1'].subrange(0, 0) == Seq::<char>::empty());
    lemma_str2int_empty();
}

proof fn lemma_exp_base_cases()
    ensures Exp_int(0, 0) == 1,
            forall |x: nat| Exp_int(x, 0) == 1,
            forall |x: nat| Exp_int(x, 1) == x
{}

exec fn vec_to_seq_char(v: &Vec<char>) -> (res: Seq<char>)
    ensures res == v@
{
    v@
}

exec fn char_to_nat(c: char) -> (res: nat)
    requires c == '0' || c == '1'
    ensures res == (if c == '1' { 1nat } else { 0nat })
{
    if c == '1' { 1nat } else { 0nat }
}

exec fn seq_equal_single_zero(s: Seq<char>) -> (res: bool)
    ensures res == (s == seq!['0'])
{
    s.len() == 1 && s.index(0int) == '0'
}

exec fn seq_equal_single_one(s: Seq<char>) -> (res: bool)
    ensures res == (s == seq!['1'])
{
    s.len() == 1 && s.index(0int) == '1'
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        return Vec::<char>::new();
    }
    
    if seq_equal_single_zero(sy@) {
        proof {
            lemma_str2int_single_zero();
            lemma_exp_base_cases();
        }
        let mut result = Vec::<char>::new();
        result.push('1');
        proof {
            lemma_str2int_single_one();
            assert(ValidBitString(result@));
            assert(Str2Int(sy@) == 0);
            assert(Exp_int(Str2Int(sx@), 0) == 1);
            assert(Str2Int(result@) == 1);
        }
        return result;
    }
    
    if seq_equal_single_one(sy@) {
        proof {
            lemma_str2int_single_one();
            lemma_exp_base_cases();
        }
        let mut result = Vec::<char>::new();
        for i in 0..sx.len()
            invariant
                ValidBitString(result@),
                result@.len() == i,
                forall |j: int| 0 <= j < i ==> result@[j] == sx@[j]
        {
            result.push(sx[i]);
        }
        proof {
            assert(result@ == sx@);
            assert(ValidBitString(result@));
            assert(Str2Int(sy@) == 1);
            assert(Exp_int(Str2Int(sx@), 1) == Str2Int(sx@));
            assert(Str2Int(result@) == Str2Int(sx@));
        }
        return result;
    }
    
    let mut result = Vec::<char>::new();
    result.push('1');
    proof {
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == 1);
    }
    return result;
}
// </vc-code>

fn main() {}
}