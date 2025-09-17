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
spec fn CharBit(c: char) -> nat {
    if c == '1' { 1 } else { 0 }
}

proof fn lemma_str2int_all_zero(s: Seq<char>)
    requires s.len() >= 0
    ensures (forall |i: int| 0 <= i && i < s.len() ==> s.index(i) == '0') ==> Str2Int(s) == 0
{
    if s.len() == 0 {
    } else {
        lemma_str2int_all_zero(s.subrange(0, s.len() as int - 1));
        if s.index(s.len() as int - 1) == '0' {
            assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + 0);
            assert((forall |i: int| 0 <= i && i < s.subrange(0, s.len() as int - 1).len() ==> s.subrange(0, s.len() as int - 1).index(i) == '0'));
            assert(Str2Int(s.subrange(0, s.len() as int - 1)) == 0);
            assert(Str2Int(s) == 0);
        } else {
        }
    }
}

proof fn lemma_str2int_concat(s: Seq<char>, b: char)
    ensures Str2Int(s + seq![b]) == 2 * Str2Int(s) + CharBit(b)
{
    if s.len() == 0 {
        // s = [], so s + [b] = [b]
        assert(Str2Int(seq![b]) == (if b == '1' { 1 } else { 0 }));
        assert(2 * Str2Int(seq![]) + CharBit(b) == CharBit(b));
    } else {
        let t = s + seq![b];
        // t.subrange(0, t.len()-1) == s
        assert(t.subrange(0, t.len() as int - 1) == s);
        // last element of t is b
        assert(t.index(t.len() as int - 1) == b);
        // unfold definition
        assert(Str2Int(t) == 2 * Str2Int(t.subrange(0, t.len() as int - 1)) + (if t.index(t.len() as int - 1) == '1' { 1 } else { 0 }));
        assert(Str2Int(t) == 2 * Str2Int(s) + CharBit(b));
    }
}

// Convert a natural number to a sequence of '0'/'1' characters,
// with the least-significant bit at the end of the sequence.
// e.g., NatToSeq(6) == seq!['1','1','0'] because 6 = (1*2 + 1)*2 + 0 = "110"
spec fn NatToSeq(n: nat) -> Seq<char>
  decreases n
{
    if n == 0 {
        seq![]
    } else {
        let b = if n % 2 == 1 { '1' } else { '0' };
        NatToSeq(n / 2) + seq![b]
    }
}

proof fn lemma_natseq_valid(n: nat)
    ensures ValidBitString(NatToSeq(n))
{
    if n == 0 {
    } else {
        lemma_natseq_valid(n / 2);
        // last char is either '0' or '1' by construction
    }
}

proof fn lemma_natseq_correct(n: nat)
    ensures Str2Int(NatToSeq(n)) == n
    decreases n
{
    if n == 0 {
        assert(Str2Int(seq![]) == 0);
    } else {
        lemma_natseq_correct(n / 2);
        // NatToSeq(n) = NatToSeq(n/2) + seq![b]
        let s = NatToSeq(n / 2);
        let b = if n % 2 == 1 { '1' } else { '0' };
        lemma_str2int_concat(s, b);
        assert(Str2Int(s + seq![b]) == 2 * Str2Int(s) + CharBit(b));
        assert(Str2Int(s) == n / 2);
        assert(CharBit(b) == (if n % 2 == 1 { 1 } else { 0 }));
        // property of division/remainder: n == 2*(n/2) + (n % 2)
        assert(n == 2 * (n / 2) + (n % 2));
        assert(Str2Int(s + seq![b]) == n);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    // compute numeric values n1 and n2 corresponding to s1 and s2
    let mut n1: nat = 0;
    let mut i: usize = 0;
    while i < s1.len()
        invariant i <= s1.len()
        invariant n1 == Str2Int(s1@.subrange(0, i as int))
        decreases (s1.len() - i) as nat
    {
        let old_n1 = n1;
        let old_i = i;
        let c = s1[i];
        if c == '1' {
            n1 = n1 * 2 + 1;
        } else {
            n1 = n1 * 2;
        }
        i += 1;
        proof {
            // old_n1 == Str2Int(s1@.subrange(0, old_i as int))
            assert(old_n1 == Str2Int(s1@.subrange(0, old_i as int)));
            // relate sequence element and local char
            assert(s1@.index(old_i as int) == c);
            // subrange extension: subrange(0, old_i+1) == subrange(0, old_i) + [s1@.index(old_i)]
            assert(s1@.subrange(0, i as int) == s1@.subrange(0, old_i as int) + seq![s1@.index(old_i as int)]);
            // apply concat lemma
            lemma_str2int_concat(s1@.subrange(0, old_i as int), s1@.index(old_i as int));
            assert(Str2Int(s1@.subrange(0, i as int)) == 2 * Str2Int(s1@.subrange(0, old_i as int)) + CharBit(s1@.index(old_i as int)));
            // relate updated n1 with CharBit
            if c == '1' {
                assert(n1 == old_n1 * 2 + 1);
                assert(CharBit(s1@.index(old_i as int)) == 1);
            } else {
                assert(n1 == old_n1 * 2);
                assert(CharBit(s1@.index(old_i as int)) == 0);
            }
            assert(n1 == Str2Int(s1@.subrange(0, i as int)));
        }
    }

    let mut n2: nat = 0;
    let mut j: usize = 0;
    while j < s2.len()
        invariant j <= s2.len()
        invariant n2 == Str2Int(s2@.subrange(0, j as int))
        decreases (s2.len() - j) as nat
    {
        let old_n2 = n2;
        let old_j = j;
        let c2 = s2[j];
        if c2 == '1' {
            n2 = n2 * 2 + 1;
        } else {
            n2 = n2 * 2;
        }
        j += 1;
        proof {
            assert(old_n2 == Str2Int(s2@.subrange(0, old_j as int)));
            assert(s2@.index(old_j as int) == c2);
            assert(s2@.subrange(0, j as int) == s2@.subrange(0, old_j as int) + seq![s2@.index(old_j as int)]);
            lemma_str2int_concat(s2@.subrange(0, old_j as int), s2@.index(old_j as int));
            assert(Str2Int(s2@.subrange(0, j as int)) == 2 * Str2Int(s2@.subrange(0, old_j as int)) + CharBit(s2@.index(old_j as int)));
            if c2 == '1' {
                assert(n2 == old_n2 * 2 + 1);
                assert(CharBit(s2@.index(old_j as int)) == 1);
            } else {
                assert(n2 == old_n2 * 2);
                assert(CharBit(s2@.index(old_j as int)) == 0);
            }
            assert(n2 == Str2Int(s2@.subrange(0, j as int)));
        }
    }

    let prod: nat = n1 * n2;

    proof {
        lemma_natseq_valid(prod);
        lemma_natseq_correct(prod);
    }
    let seq_res = NatToSeq(prod);
    let res = Vec::from_seq(seq_res);
    assert(ValidBitString(res@));
    assert(Str2Int(res@) == prod);
    res
}
// </vc-code>

fn main() {}
}