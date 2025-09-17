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
/* helper modified by LLM (iteration 2): define BitsOf to produce binary representation of a nat as a Seq<char> */
spec fn BitsOf(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 { Seq::empty() } else { BitsOf(n / 2).push(if n % 2 == 1 { '1' } else { '0' }) }
}

/* helper modified by LLM (iteration 2): lemma showing ValidBitString is preserved by push */
proof fn lemma_valid_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        ValidBitString(s.push(c)),
{
    let sp = s.push(c);
    assert(sp.len() == s.len() + 1);
    assert forall |i: int|
        0 <= i && i < sp.len() as int ==> sp.index(i) == '0' || sp.index(i) == '1'
    by
    {
        if i < s.len() as int {
            assert(sp.index(i) == s.index(i));
            assert(0 <= i && i < s.len() as int);
            assert(ValidBitString(s));
            assert(s.index(i) == '0' || s.index(i) == '1');
        } else {
            assert(i == s.len() as int);
            assert(sp.index(i) == c);
            assert(c == '0' || c == '1');
        }
    }
}

/* helper modified by LLM (iteration 2): lemma relating Str2Int after pushing a bit */
proof fn lemma_str2int_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat }),
{
    lemma_valid_push(s, c);
    let sp = s.push(c);
    assert(sp.len() > 0);
    assert(sp.subrange(0, sp.len() as int - 1) == s);
    assert(sp.index(sp.len() as int - 1) == c);
    assert(Str2Int(sp) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat }));
}

/* helper modified by LLM (iteration 2): lemma that BitsOf produces a valid bitstring whose integer value equals the input */
proof fn lemma_bits_of_valid_and_value(n: nat)
    ensures
        ValidBitString(BitsOf(n)),
        Str2Int(BitsOf(n)) == n,
    decreases n
{
    if n == 0 {
    } else {
        lemma_bits_of_valid_and_value(n / 2);
        let rest = BitsOf(n / 2);
        let c = if n % 2 == 1 { '1' } else { '0' };
        lemma_valid_push(rest, c);
        lemma_str2int_push(rest, c);
        assert(Str2Int(BitsOf(n)) == 2 * Str2Int(rest) + (if c == '1' { 1nat } else { 0nat }));
        assert(Str2Int(rest) == n / 2);
        if n % 2 == 1 {
            assert((if c == '1' { 1nat } else { 0nat }) == 1nat);
        } else {
            assert((if c == '1' { 1nat } else { 0nat }) == 0nat);
        }
        assert(2 * (n / 2) + (n % 2) == n);
    }
}

/* helper modified by LLM (iteration 5): convert Seq<char> to Vec<char> by iterating and pushing, preserving the view */
exec fn to_vec_from_seq_char(s: Seq<char>) -> (v: Vec<char>)
    ensures
        v@ == s,
{
    let mut v = Vec::<char>::new();
    let mut i: int = 0;
    while i < s.len() as int
        invariant
            0 <= i && i <= s.len() as int,
            v@ == s.subrange(0, i),
        decreases s.len() as int - i
    {
        let c = s.index(i);
        v.push(c);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute modular exponent and return its binary representation as Vec<char> */
    let n_mod = Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@);
    proof {
        lemma_bits_of_valid_and_value(n_mod);
    }
    let seq = BitsOf(n_mod);
    let res_vec = to_vec_from_seq_char(seq);
    res_vec
}
// </vc-code>

fn main() {}
}
