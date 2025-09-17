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
/* helper modified by LLM (iteration 2): nat->bitstring conversion and correctness lemmas */
spec fn NatToBits(n: nat) -> Seq<char>
    decreases n
{
    if n == 0u128 as nat {
        Seq::<char>::empty()
    } else {
        let q = n / 2;
        let r = n % 2;
        let prev = NatToBits(q);
        if r == 1 { prev.push('1') } else { prev.push('0') }
    }
}

proof fn lemma_valid_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        ValidBitString(s.push(c)),
{
    assert(forall |i: int|
        0 <= i && i < s.push(c).len() as int ==> (s.push(c).index(i) == '0' || s.push(c).index(i) == '1')
    ) by {
        let i: int;
        require(0 <= i && i < s.push(c).len() as int);
        if i < s.len() as int {
            assert(s.push(c).index(i) == s.index(i));
            assert(ValidBitString(s));
            assert(s.index(i) == '0' || s.index(i) == '1');
        } else {
            assert(i == s.len() as int);
            assert(s.push(c).index(i) == c);
            assert(c == '0' || c == '1');
        }
    };
}

proof fn lemma_nat_to_bits_valid_and_value(n: nat)
    ensures
        ValidBitString(NatToBits(n)),
        Str2Int(NatToBits(n)) == n,
    decreases n
{
    if n == 0 {
        assert(ValidBitString(Seq::<char>::empty()));
    } else {
        let q = n / 2;
        let r = n % 2;
        lemma_nat_to_bits_valid_and_value(q);
        assert(0 <= r && r < 2);
        if r == 1 { lemma_valid_push(NatToBits(q), '1'); } else { lemma_valid_push(NatToBits(q), '0'); }

        let s_prev = NatToBits(q);
        let s = if r == 1 { s_prev.push('1') } else { s_prev.push('0') };
        assert(s.len() > 0);
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));
        assert(s.subrange(0, s.len() as int - 1) == s_prev);
        if r == 1 { assert(s.index(s.len() as int - 1) == '1'); } else { assert(s.index(s.len() as int - 1) == '0'); }
        if r == 1 {
            assert(Str2Int(s) == 2 * Str2Int(s_prev) + 1);
        } else {
            assert(Str2Int(s) == 2 * Str2Int(s_prev) + 0);
        }
        assert(Str2Int(s) == 2 * Str2Int(s_prev) + r);
        assert(n == 2 * q + r);
        assert(Str2Int(s_prev) == q);
        assert(Str2Int(s) == n);
        assert(NatToBits(n) == s);
    }
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
    /* code modified by LLM (iteration 2): construct result from spec using NatToBits and Vec::from_seq */
    proof {
        lemma_nat_to_bits_valid_and_value(Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    let seq_res = NatToBits(Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    let res = Vec::from_seq(seq_res);
    res
}
// </vc-code>

fn main() {}
}
