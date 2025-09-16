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
/* helper modified by LLM (iteration 6): predicate for bit characters */
spec fn is_bit(c: char) -> bool { c == '0' || c == '1' }

/* helper modified by LLM (iteration 6): convert a bit character to its nat value */
spec fn bit_to_nat(c: char) -> nat { if c == '1' { 1nat } else { 0nat } }

/* helper modified by LLM (iteration 6): convert a nat to its binary bitstring (most significant bit first) */
spec fn nat_to_bits(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        let rest = nat_to_bits(n / 2);
        let c = if n % 2 == 1 { '1' } else { '0' };
        rest.push(c)
    }
}

/* helper modified by LLM (iteration 6): correctness of nat_to_bits (valid bitstring and value equality) */
proof fn lemma_nat_to_bits_value(n: nat)
    ensures
        ValidBitString(nat_to_bits(n)),
        Str2Int(nat_to_bits(n)) == n,
    decreases n
{
    if n == 0 {
        // Str2Int("") == 0 by definition, ValidBitString holds vacuously
    } else {
        lemma_nat_to_bits_value(n / 2);
        let rest = nat_to_bits(n / 2);
        let c = if n % 2 == 1 { '1' } else { '0' };
        assert(nat_to_bits(n) == rest.push(c));

        // Prove validity of the resulting bitstring
        assert forall |i: int|
            0 <= i && i < nat_to_bits(n).len() as int
            implies
                (nat_to_bits(n).index(i) == '0' || nat_to_bits(n).index(i) == '1')
        by {
            if i < rest.len() as int {
                assert(nat_to_bits(n) == rest.push(c));
                assert(nat_to_bits(n).index(i) == rest.index(i));
                assert(ValidBitString(rest));
            } else {
                assert(i == rest.len() as int);
                assert(nat_to_bits(n).index(i) == c);
                assert(c == '0' || c == '1');
            }
        };

        // Compute Str2Int(rest.push(c)) via definition
        let t = rest.push(c);
        assert(nat_to_bits(n) == t);
        assert(t.subrange(0, t.len() as int - 1) == rest);
        assert(t.index(t.len() as int - 1) == c);
        assert(Str2Int(t) == 2 * Str2Int(rest) + (if c == '1' { 1nat } else { 0nat }));

        // Use IH: Str2Int(rest) == n/2
        assert(Str2Int(rest) == n / 2);

        // c chosen from n % 2, hence (if c == '1' {1} else {0}) == n % 2
        proof {
            if n % 2 == 1 {
                assert(c == '1');
                assert((if c == '1' { 1nat } else { 0nat }) == 1nat);
                assert(n % 2 == 1nat);
            } else {
                assert(c == '0');
                assert((if c == '1' { 1nat } else { 0nat }) == 0nat);
                assert(n % 2 == 0nat);
            }
        }

        // Conclude
        assert(Str2Int(nat_to_bits(n)) == 2 * (n / 2) + (n % 2));
        assert(2 * (n / 2) + (n % 2) == n);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 6): construct result from nat_to_bits via Vec::from and justify with lemma */
    proof {
        lemma_nat_to_bits_value(Str2Int(s1@) * Str2Int(s2@));
    }
    let res: Vec<char> = Vec::<char>::from(nat_to_bits(Str2Int(s1@) * Str2Int(s2@)));
    res
}
// </vc-code>

fn main() {}
}
