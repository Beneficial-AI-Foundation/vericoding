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
/* helper modified by LLM (iteration 5): bitstring conversion from nat using recursion */
spec fn NatToBits(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        let q = n / 2;
        let r = n % 2;
        let prev = NatToBits(q);
        if r == 1 { prev.push('1') } else { prev.push('0') }
    }
}

/* helper modified by LLM (iteration 5): pushing a valid bit preserves validity */
proof fn lemma_valid_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        ValidBitString(s.push(c)),
{
    assert forall |i: int|
        0 <= i && i < s.push(c).len() as int ==> (s.push(c).index(i) == '0' || s.push(c).index(i) == '1')
    by
    {
        if 0 <= i && i < s.push(c).len() as int {
            if i < s.len() as int {
                assert(s.push(c).index(i) == s.index(i));
                assert(ValidBitString(s));
                assert(s.index(i) == '0' || s.index(i) == '1');
            } else {
                assert(i == s.len() as int);
                assert(s.push(c).index(i) == c);
                assert(c == '0' || c == '1');
            }
        }
    };
}

/* helper modified by LLM (iteration 5): NatToBits produces valid bitstrings and matches Str2Int value */
proof fn lemma_nat_to_bits_valid_and_value(n: nat)
    ensures
        ValidBitString(NatToBits(n)),
        Str2Int(NatToBits(n)) == n,
    decreases n
{
    if n == 0 {
        assert(ValidBitString(Seq::<char>::empty()));
        assert(Str2Int(Seq::<char>::empty()) == 0);
    } else {
        let q = n / 2;
        let r = n % 2;
        lemma_nat_to_bits_valid_and_value(q);
        assert(0 <= r && r < 2);
        if r == 1 { lemma_valid_push(NatToBits(q), '1'); } else { lemma_valid_push(NatToBits(q), '0'); }

        let s_prev = NatToBits(q);
        let s = if r == 1 { s_prev.push('1') } else { s_prev.push('0') };
        assert(s.len() > 0);
        assert(s.subrange(0, s.len() as int - 1) == s_prev);
        if r == 1 { assert(s.index(s.len() as int - 1) == '1'); } else { assert(s.index(s.len() as int - 1) == '0'); }
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));
        if r == 1 {
            assert(Str2Int(s) == 2 * Str2Int(s_prev) + 1);
        } else {
            assert(Str2Int(s) == 2 * Str2Int(s_prev) + 0);
        }
        assert(Str2Int(s_prev) == q);
        assert(Str2Int(s) == 2 * q + r);
        assert(n == 2 * q + r);
        assert(Str2Int(s) == n);
        assert(NatToBits(n) == s);
    }
}

/* helper modified by LLM (iteration 6): validity is preserved for any prefix (subrange) of a valid bitstring */
proof fn lemma_valid_subrange(s: Seq<char>, i: int)
    requires
        ValidBitString(s),
        0 <= i,
        i <= s.len() as int,
    ensures
        ValidBitString(s.subrange(0, i)),
{
    assert forall |k: int|
        0 <= k && k < s.subrange(0, i).len() as int ==> (s.subrange(0, i).index(k) == '0' || s.subrange(0, i).index(k) == '1')
    by
    {
        if 0 <= k && k < s.subrange(0, i).len() as int {
            assert(k < i);
            assert(s.subrange(0, i).index(k) == s.index(k));
            assert(ValidBitString(s));
        }
    };
}

/* helper modified by LLM (iteration 6): extending a prefix by the next element equals the longer prefix */
proof fn lemma_subrange_push_next(s: Seq<char>, i: int)
    requires
        0 <= i,
        i < s.len() as int,
    ensures
        s.subrange(0, i).push(s.index(i)) == s.subrange(0, i + 1),
{
    let lhs = s.subrange(0, i).push(s.index(i));
    let rhs = s.subrange(0, i + 1);
    assert(lhs.len() as int == i + 1);
    assert(rhs.len() as int == i + 1);
    assert forall |k: int|
        0 <= k && k < lhs.len() as int ==> lhs.index(k) == rhs.index(k)
    by
    {
        if k < i {
            assert(lhs.index(k) == s.subrange(0, i).index(k));
            assert(s.subrange(0, i).index(k) == s.index(k));
            assert(rhs.index(k) == s.index(k));
        } else {
            assert(k == i);
            assert(lhs.index(k) == s.index(i));
            assert(rhs.index(k) == s.index(i));
        }
    };
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
    /* code modified by LLM (iteration 6): replace Vec::from_seq with manual construction via loop and maintain invariants linking to Seq */
    let val = Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@);
    proof { lemma_nat_to_bits_valid_and_value(val); }
    let seq_res = NatToBits(val);
    let mut res: Vec<char> = Vec::new();

    let mut i: int = 0;
    let len_i: int = seq_res.len() as int;

    // Establish initial invariant: res@ equals empty prefix
    proof {
        assert(res@ == seq_res.subrange(0, i));
        lemma_valid_subrange(seq_res, i);
        assert(ValidBitString(res@));
    }

    while i < len_i
        invariant
            0 <= i && i <= len_i,
            res@ == seq_res.subrange(0, i),
            ValidBitString(res@),
        decreases len_i - i
    {
        let ch = seq_res.index(i);
        let old_view = res@;
        res.push(ch);
        proof {
            // After push: res@ == old_view.push(ch)
            assert(res@ == old_view.push(ch));
            assert(old_view == seq_res.subrange(0, i));
            lemma_subrange_push_next(seq_res, i);
            assert(res@ == seq_res.subrange(0, i + 1));
        }
        i = i + 1;
        proof {
            lemma_valid_subrange(seq_res, i);
            assert(ValidBitString(seq_res.subrange(0, i)));
            assert(ValidBitString(res@));
        }
    }

    proof {
        assert(i == len_i);
        assert(res@ == seq_res.subrange(0, len_i));
        assert(seq_res.subrange(0, len_i) == seq_res);
        assert(Str2Int(res@) == Str2Int(seq_res));
        assert(Str2Int(seq_res) == val);
        assert(ValidBitString(res@));
    }

    res
}
// </vc-code>

fn main() {}
}
