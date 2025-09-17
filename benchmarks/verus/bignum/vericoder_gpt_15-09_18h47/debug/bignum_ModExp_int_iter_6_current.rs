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
/* helper modified by LLM (iteration 6): binary representation of a nat as a bitstring (Seq<char> of '0'/'1') */
spec fn Int2StrBits(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        let b: char = if n % 2 == 1 { '1' } else { '0' };
        Int2StrBits(n / 2) + seq![b]
    }
}

/* helper modified by LLM (iteration 6): proof that Int2StrBits yields a ValidBitString */
proof fn lemma_Int2StrBits_valid(n: nat)
    ensures
        ValidBitString(Int2StrBits(n)),
    decreases n
{
    if n == 0 {
        // empty sequence is vacuously a valid bitstring
    } else {
        lemma_Int2StrBits_valid(n / 2);
        let t = Int2StrBits(n / 2);
        let b: char = if n % 2 == 1 { '1' } else { '0' };
        let s = t + seq![b];
        assert(Int2StrBits(n) == s);
        assert(s.len() == t.len() + 1);
        assert_forall_by(|i: int|
            requires
                0 <= i,
                i < s.len() as int,
            ensures
                s.index(i) == '0' || s.index(i) == '1',
        {
            let tlen: int = t.len() as int;
            if i < tlen {
                assert((t + seq![b]).index(i) == t.index(i));
                assert(ValidBitString(t));
                assert(t.index(i) == '0' || t.index(i) == '1');
            } else {
                assert(s.len() as int == tlen + 1);
                assert(i == tlen);
                assert((t + seq![b]).index(i) == seq![b].index(0));
                assert(seq![b].len() == 1);
                assert(seq![b].index(0) == b);
                assert(b == '0' || b == '1');
            }
        });
        assert(ValidBitString(s));
    }
}

/* helper modified by LLM (iteration 6): proof that Str2Int(Int2StrBits(n)) == n */
proof fn lemma_Str2Int_Int2StrBits(n: nat)
    ensures
        Str2Int(Int2StrBits(n)) == n,
    decreases n
{
    if n == 0 {
        assert(Int2StrBits(0) == Seq::<char>::empty());
        assert(Str2Int(Int2StrBits(0)) == 0);
    } else {
        lemma_Str2Int_Int2StrBits(n / 2);
        let t = Int2StrBits(n / 2);
        let b: char = if n % 2 == 1 { '1' } else { '0' };
        let s = t + seq![b];
        assert(Int2StrBits(n) == s);
        assert(s.len() == t.len() + 1);
        let lenm1: int = s.len() as int - 1;
        assert(lenm1 == t.len() as int);
        assert(s.subrange(0, lenm1) == t);
        assert(s.index(lenm1) == (t + seq![b]).index(t.len() as int));
        assert((t + seq![b]).index(t.len() as int) == seq![b].index(0));
        assert(seq![b].index(0) == b);
        let bit: nat = if b == '1' { 1nat } else { 0nat };
        assert(Str2Int(s) == 2 * Str2Int(t) + bit);
        assert(Str2Int(t) == n / 2);
        if n % 2 == 1 {
            assert(bit == 1nat);
        } else {
            assert(bit == 0nat);
        }
        assert(Str2Int(s) == 2 * (n / 2) + (n % 2));
        assert(2 * (n / 2) + (n % 2) == n);
        assert(Str2Int(Int2StrBits(n)) == n);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 6): compute modular exponent, convert to bitstring, and return as Vec<char> with proofs */
    let n_mod: nat = Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@);
    proof { lemma_Int2StrBits_valid(n_mod); }
    let sres: Seq<char> = Int2StrBits(n_mod);
    proof { lemma_Str2Int_Int2StrBits(n_mod); }
    let res_vec: Vec<char> = Vec::from_seq(sres);
    res_vec
}
// </vc-code>

fn main() {}
}
