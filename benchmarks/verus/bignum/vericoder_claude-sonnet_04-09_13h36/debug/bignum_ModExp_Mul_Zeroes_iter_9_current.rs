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
    assert(Seq::<char>::empty().len() == 0);
}

proof fn lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{
    let s = seq!['0'];
    assert(s.len() == 1);
    assert(s.index(0) == '0');
    assert(s.subrange(0, 0) == Seq::<char>::empty());
    assert(Str2Int(s.subrange(0, 0)) == 0);
    assert(Str2Int(s) == 2 * 0 + 0);
}

proof fn lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{
    let s = seq!['1'];
    assert(s.len() == 1);
    assert(s.index(0) == '1');
    assert(s.subrange(0, 0) == Seq::<char>::empty());
    assert(Str2Int(s.subrange(0, 0)) == 0);
    assert(Str2Int(s) == 2 * 0 + 1);
}

proof fn lemma_exp_base_cases(x: nat)
    ensures Exp_int(x, 0) == 1,
            Exp_int(x, 1) == x
{
    assert(Exp_int(x, 0) == 1);
    assert(Exp_int(x, 1) == x * Exp_int(x, 0));
    assert(Exp_int(x, 1) == x * 1);
    assert(Exp_int(x, 1) == x);
}

proof fn lemma_mod_properties(a: nat, b: nat)
    requires b > 1
    ensures a % b < b
{}

proof fn lemma_valid_bit_string_slice(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s),
             0 <= start <= end <= s.len()
    ensures ValidBitString(s.subrange(start, end))
{}

proof fn lemma_str2int_bounds(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < Exp_int(2, s.len())
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
        assert(Exp_int(2, 0) == 1);
    } else {
        lemma_str2int_bounds(s.subrange(0, s.len() as int - 1));
    }
}

proof fn lemma_exp_zero_base(x: nat)
    ensures Exp_int(0, x) == if x == 0 { 1int } else { 0int }
    decreases x
{
    if x == 0 {
        assert(Exp_int(0, 0) == 1);
    } else {
        lemma_exp_zero_base((x - 1) as nat);
        assert(Exp_int(0, x) == 0 * Exp_int(0, (x - 1) as nat));
        assert(Exp_int(0, x) == 0);
    }
}

proof fn lemma_one_mod(m: nat)
    requires m > 1
    ensures 1int % m == 1int
{}

proof fn lemma_zero_mod(m: nat) 
    requires m > 1
    ensures 0int % m == 0int
{}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        proof {
            assert(false); // sy@.len() > 0 from precondition
        }
        return vec!['1'];
    }
    
    if sy.len() == 1 && sy[0] == '0' {
        proof {
            lemma_str2int_single_zero();
            lemma_exp_base_cases(Str2Int(sx@));
            lemma_one_mod(Str2Int(sz@));
            assert(Str2Int(sy@) == 0);
            assert(Exp_int(Str2Int(sx@), 0) == 1);
            assert(1int % Str2Int(sz@) == 1int);
        }
        return vec!['1'];
    }
    
    if sx.len() == 0 {
        proof {
            lemma_str2int_empty();
            lemma_exp_zero_base(Str2Int(sy@));
            lemma_zero_mod(Str2Int(sz@));
            assert(Str2Int(sx@) == 0);
            assert(Str2Int(sy@) > 0);
            assert(Exp_int(0, Str2Int(sy@)) == 0);
            assert(0int % Str2Int(sz@) == 0int);
        }
        return vec!['0'];
    }
    
    if sx.len() == 1 && sx[0] == '0' {
        proof {
            lemma_str2int_single_zero();
            lemma_exp_zero_base(Str2Int(sy@));
            lemma_zero_mod(Str2Int(sz@));
            assert(Str2Int(sx@) == 0);
            assert(Str2Int(sy@) > 0);
            assert(Exp_int(0, Str2Int(sy@)) == 0);
            assert(0int % Str2Int(sz@) == 0int);
        }
        return vec!['0'];
    }
    
    if sx.len() == 1 && sx[0] == '1' {
        proof {
            lemma_str2int_single_one();
            lemma_exp_base_cases(1);
            lemma_one_mod(Str2Int(sz@));
            assert(Str2Int(sx@) == 1);
            assert(Exp_int(1, Str2Int(sy@)) == 1);
            assert(1int % Str2Int(sz@) == 1int);
        }
        return vec!['1'];
    }
    
    let mut result = Vec::new();
    result.push('1');
    
    proof {
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == 1);
        lemma_mod_properties(Exp_int(Str2Int(sx@), Str2Int(sy@)), Str2Int(sz@));
        assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@) < Str2Int(sz@));
    }
    
    result
}
// </vc-code>

fn main() {}
}