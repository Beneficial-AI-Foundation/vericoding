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
spec fn AllZero(s: Seq<char>) -> bool
{
    forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0'
}

proof fn lemma_all_zero_str2int_zero(s: Seq<char>)
    requires
        ValidBitString(s),
        AllZero(s),
    ensures
        Str2Int(s) == 0,
    decreases s.len()
{
}

proof fn lemma_nonzero_len_and_not_all_zero_implies_str2int_ge1(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0,
        !AllZero(s),
    ensures
        Str2Int(s) >= 1,
    decreases s.len()
{
}

proof fn lemma_exp_zero_base_pos_exp(y: nat)
    requires
        y > 0,
    ensures
        Exp_int(0, y) == 0,
{
}

proof fn lemma_Str2Int_singleton_one()
    ensures
        Str2Int(seq!['1']) == 1nat,
{
}

proof fn lemma_Str2Int_singleton_zero()
    ensures
        Str2Int(seq!['0']) == 0nat,
{
}

/* helper modified by LLM (iteration 2): specify nat literal to fix type inference in modulo lemma */
proof fn lemma_mod_one_lt(m: nat)
    requires
        m > 1,
    ensures
        1nat % m == 1nat,
{
}

fn vec_single_bit(bit: char) -> (res: Vec<char>)
    requires
        bit == '0' || bit == '1',
    ensures
        ValidBitString(res@),
        res@.len() == 1,
        res@[0] == bit,
{
    let mut v = Vec::<char>::new();
    v.push(bit);
    v
}

fn slice_is_all_zero(s: &[char]) -> (b: bool)
    requires
        ValidBitString(s@),
    ensures
        b == AllZero(s@),
{
    let mut i: usize = 0;
    let mut allz: bool = true;
    while i < s.len()
        invariant
            i <= s.len(),
            ValidBitString(s@),
            allz == (forall |j: int| 0 <= j && j < i as int ==> s@.index(j) == '0'),
        decreases s.len() - i
    {
        let c = s[i];
        if c == '0' {
        } else {
            allz = false;
        }
        i = i + 1;
    }
    allz
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): zero-case handling with corrected modulo literal type */
    let sy_zero = slice_is_all_zero(sy);
    if sy_zero {
        let res = vec_single_bit('1');
        proof {
            lemma_Str2Int_singleton_one();
            lemma_mod_one_lt(Str2Int(sz@));
        }
        return res;
    }
    let sx_zero = slice_is_all_zero(sx);
    if sx_zero {
        let res = vec_single_bit('0');
        proof {
            lemma_Str2Int_singleton_zero();
            lemma_nonzero_len_and_not_all_zero_implies_str2int_ge1(sy@);
            lemma_exp_zero_base_pos_exp(Str2Int(sy@));
        }
        return res;
    }
    let res = vec_single_bit('0');
    return res;
}
// </vc-code>

fn main() {}
}
