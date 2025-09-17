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

lemma_str2int_all_zero(s: Seq<char>)
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

lemma_str2int_concat(s: Seq<char>, b: char)
    ensures Str2Int(s + seq![b]) == 2 * Str2Int(s) + CharBit(b)
{
    if s.len() == 0 {
        assert(Str2Int(seq![b]) == (if b == '1' { 1 } else { 0 }));
        assert(2 * Str2Int(seq![]) + CharBit(b) == CharBit(b));
    } else {
        lemma_str2int_concat(s.subrange(0, s.len() as int - 1), s.index(s.len() as int - 1));
    }
}

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

spec fn NatToBits(n: nat) -> Seq<char>
  decreases n
{
    if n == 0 {
        seq!['0']
    } else {
        let prefix = NatToBits(n / 2);
        prefix + seq![ if n % 2 == 1 { '1' } else { '0' } ]
    }
}

lemma_nat_to_bits_correct(n: nat)
    ensures Str2Int(NatToBits(n)) == n
{
    if n == 0 {
        lemma_str2int_all_zero(seq!['0']);
        assert(Str2Int(seq!['0']) == 0);
    } else {
        lemma_nat_to_bits_correct(n / 2);
        let bit = if n % 2 == 1 { '1' } else { '0' };
        lemma_str2int_concat(NatToBits(n / 2), bit);
        assert(Str2Int(NatToBits(n / 2) + seq![bit]) == 2 * Str2Int(NatToBits(n / 2)) + CharBit(bit));
        assert(Str2Int(NatToBits(n / 2)) == n / 2);
        assert(2 * (n / 2) + CharBit(bit) == n);
    }
}

// New helper lemmas for prepending and division arithmetic used in the implementation proof

lemma_str2int_prepend(c: char, s: Seq<char>)
    ensures Str2Int(seq![c] + s) == CharBit(c) * Exp_int(2, s.len()) + Str2Int(s)
{
    if s.len() == 0 {
        // seq![c] + [] = [c]; Str2Int([c]) = CharBit(c)
        assert(Str2Int(seq![c]) == (if c == '1' { 1 } else { 0 }));
        assert(CharBit(c) * Exp_int(2, 0) + Str2Int(seq![]) == CharBit(c));
    } else {
        let s0 = s.subrange(0, s.len() as int - 1);
        let last = s.index(s.len() as int - 1);
        // seq![c] + s = (seq![c] + s0) + [last]
        lemma_str2int_prepend(c, s0);
        lemma_str2int_concat(seq![c] + s0, last);
        // Str2Int((seq![c]+s0)+[last]) = 2 * Str2Int(seq![c]+s0) + CharBit(last)
        // and Str2Int(seq![c]+s0) = CharBit(c) * 2^{s0.len()} + Str2Int(s0)
        // combine to get desired result
    }
}

lemma_divition_mul_property(p: nat, l: nat)
    ensures (p / 2) * Exp_int(2, l + 1) + (p % 2) * Exp_int(2, l) == p * Exp_int(2, l)
{
    // p = 2*(p/2) + p%2
    assert(p == 2 * (p / 2) + (p % 2));
    // multiply both sides by 2^l
    assert(p * Exp_int(2, l) == (2 * (p / 2) + (p % 2)) * Exp_int(2, l));
    assert(p * Exp_int(2, l) == (p / 2) * Exp_int(2, l + 1) + (p % 2) * Exp_int(2, l));
}

lemma_charbit_parity(p: nat)
    ensures CharBit(if p % 2 == 1 { '1' } else { '0' }) == p % 2
{
    if p % 2 == 1 {
        assert(CharBit('1') == 1);
        assert(1 == p % 2);
    } else {
        assert(CharBit('0') == 0);
        assert(0 == p % 2);
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
    // implementation of Mul
    let len1 = s1.len();
    let len2 = s2.len();

    // compute numeric values a1 and a2 corresponding to s1 and s2
    let mut i: usize = 0;
    let mut a1: nat = 0;
    while i < len1
        invariant 0 <= i && i <= len1
        invariant a1 == Str2Int(s1@.subrange(0, i as int))
        decreases len1 - i
    {
        let c = s1[i];
        let bit = if c == '1' { 1 } else { 0 };
        a1 = a1 * 2 + bit;
        i += 1;
    }

    let mut j: usize = 0;
    let mut a2: nat = 0;
    while j < len2
        invariant 0 <= j && j <= len2
        invariant a2 == Str2Int(s2@.subrange(0, j as int))
        decreases len2 - j
    {
        let c = s2[j];
        let bit = if c == '1' { 1 } else { 0 };
        a2 = a2 * 2 + bit;
        j += 1;
    }

    let prod: nat = a1 * a2;

    // convert prod to binary representation (MSB-first) in a Vec<char>
    let mut res: Vec<char> = Vec::new();
    if prod == 0 {
        res.push('0');
    } else {
        // build MSB-first by inserting each LSB bit at the front
        let mut p: nat = prod;
        // invariant relates prod, current p, and res@: prod == Str2Int(res@) + p * 2^{res.len()}
        while p > 0
            invariant prod == Str2Int(res@) + p * Exp_int(2, res@.len())
            invariant forall |ii: int| 0 <= ii && ii < res@.len() ==> (res@.index(ii) == '0' || res@.index(ii) == '1')
            decreases p
        {
            let old_seq = res@;
            let old_p = p;
            let ch = if old_p % 2 == 1 { '1' } else { '0' };
            p = old_p / 2;
            res.insert(0, ch);
            proof {
                // res@ == seq![ch] + old_seq
                assert(res@ == seq![ch] + old_seq);

                // Str2Int(res@) = CharBit(ch) * 2^{old_seq.len()} + Str2Int(old_seq)
                lemma_str2int_prepend(ch, old_seq);
                assert(Str2Int(res@) == CharBit(ch) * Exp_int(2, old_seq.len()) + Str2Int(old_seq));

                // prod == Str2Int(old_seq) + old_p * 2^{old_seq.len()}
                assert(prod == Str2Int(old_seq) + old_p * Exp_int(2, old_seq.len()));

                // relate division multiplication: (old_p / 2) * 2^{old_seq.len() + 1} + (old_p % 2) * 2^{old_seq.len()} == old_p * 2^{old_seq.len()}
                lemma_divition_mul_property(old_p, old_seq.len());

                // CharBit(ch) == old_p % 2
                lemma_charbit_parity(old_p);
                assert(CharBit(ch) == old_p % 2);

                // Now compute Str2Int(res@) + p * 2^{res@.len()} and show equality to prod
                // p = old_p / 2, res@.len() = old_seq.len() + 1
                assert(Str2Int(res@) + p * Exp_int(2, res@.len()) ==
                       (CharBit(ch) * Exp_int(2, old_seq.len()) + Str2Int(old_seq)) + (old_p / 2) * Exp_int(2, old_seq.len() + 1));
                // substitute (old_p / 2) * 2^{l+1} + (old_p % 2) * 2^{l} = old_p * 2^{l}
                assert((CharBit(ch) * Exp_int(2, old_seq.len()) + Str2Int(old_seq)) + (old_p / 2) * Exp_int(2, old_seq.len() + 1) ==
                       Str2Int(old_seq) + ((old_p / 2) * Exp_int(2, old_seq.len() + 1) + (old_p % 2) * Exp_int(2, old_seq.len())));
                // replace using lemma_divition_mul_property and CharBit==old_p%2
                assert(Str2Int(old_seq) + ((old_p / 2) * Exp_int(2, old_seq.len() + 1) + (old_p % 2) * Exp_int(2, old_seq.len())) == Str2Int(old_seq) + old_p * Exp_int(2, old_seq.len()));
                // equals prod by prior invariant
                assert(Str2Int(res@) + p * Exp_int(2, res@.len()) == prod);
            }
        }
    }

    // proofs: res@ is a valid bitstring and its numeric value equals prod (which equals a1*a2)
    proof {
        assert(forall |ii: int| 0 <= ii && ii < res@.len() ==> (res@.index(ii) == '0' || res@.index(ii) == '1'));

        if prod == 0 {
            assert(res@ == seq!['0']);
            lemma_str2int_all_zero(res@);
            assert(Str2Int(res@) == 0);
            assert(prod == 0);
        } else {
            // At loop exit p == 0, and invariant gives prod == Str2Int(res@) + 0
            assert(prod == Str2Int(res@));
        }
    }

    // return result vector
    res
}
// </vc-code>

fn main() {}
}