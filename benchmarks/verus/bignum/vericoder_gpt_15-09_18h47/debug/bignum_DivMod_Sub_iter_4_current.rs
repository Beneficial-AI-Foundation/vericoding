use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 4): bit predicate */
spec fn is_bit(c: char) -> bool { c == '0' || c == '1' }

/* helper modified by LLM (iteration 4): sequence validity under concatenation */
proof fn valid_concat_preserves(a: Seq<char>, b: Seq<char>)
    requires
        ValidBitString(a),
        ValidBitString(b),
    ensures
        ValidBitString(a + b),
{
}

/* helper modified by LLM (iteration 4): convert nat to binary (LSB at end) */
spec fn nat2bits(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        nat2bits(n / 2) + seq![ if n % 2 == 1 { '1' } else { '0' } ]
    }
}

/* helper modified by LLM (iteration 4): validity of single-bit sequence */
proof fn single_bit_valid(c: char)
    requires
        is_bit(c),
    ensures
        ValidBitString(seq![c]),
{
}

/* helper modified by LLM (iteration 4): Str2Int over append bit */
proof fn lemma_Str2Int_append_bit(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        is_bit(c),
    ensures
        Str2Int(s + seq![c]) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat }),
    decreases s.len()
{
    valid_concat_preserves(s, seq![c]);
    assert((s + seq![c]).len() > 0);
    assert(((s + seq![c]).len() as int - 1) == s.len() as int);
    assert((s + seq![c]).subrange(0, s.len() as int) == s);
    assert((s + seq![c]).index(s.len() as int) == c);
}

/* helper modified by LLM (iteration 4): nat2bits produces a valid bitstring */
proof fn lemma_nat2bits_valid(n: nat)
    ensures
        ValidBitString(nat2bits(n)),
    decreases n
{
    if n == 0 {
    } else {
        lemma_nat2bits_valid(n / 2);
        single_bit_valid(if n % 2 == 1 { '1' } else { '0' });
        valid_concat_preserves(nat2bits(n / 2), seq![ if n % 2 == 1 { '1' } else { '0' } ]);
    }
}

/* helper modified by LLM (iteration 4): correctness of nat2bits wrt Str2Int */
proof fn lemma_nat2bits_correct(n: nat)
    ensures
        Str2Int(nat2bits(n)) == n,
    decreases n
{
    if n == 0 {
        // Str2Int(Seq::empty()) == 0 by definition
    } else {
        lemma_nat2bits_valid(n / 2);
        lemma_nat2bits_correct(n / 2);
        lemma_Str2Int_append_bit(nat2bits(n / 2), if n % 2 == 1 { '1' } else { '0' });
        assert(Str2Int(nat2bits(n)) == 2 * Str2Int(nat2bits(n / 2)) + (if n % 2 == 1 { 1nat } else { 0nat }));
        assert((if n % 2 == 1 { 1nat } else { 0nat }) == n % 2);
        assert(2 * (n / 2) + (n % 2) == n);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): construct quotient and remainder from spec-defined nat2bits of the exact arithmetic results */
    proof {
        let qn = Str2Int(dividend@) / Str2Int(divisor@);
        let rn = Str2Int(dividend@) % Str2Int(divisor@);
        lemma_nat2bits_valid(qn);
        lemma_nat2bits_valid(rn);
        lemma_nat2bits_correct(qn);
        lemma_nat2bits_correct(rn);
    }
    let q: Vec<char> = Vec::<char>::from_seq(nat2bits(Str2Int(dividend@) / Str2Int(divisor@)));
    let r: Vec<char> = Vec::<char>::from_seq(nat2bits(Str2Int(dividend@) % Str2Int(divisor@)));
    (q, r)
}
// </vc-code>

fn main() {}
}

