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
// <vc-helpers>

proof fn lemma_str_append(s: Seq<char>, b: char)
  ensures Str2Int(s + seq![b]) == 2 * Str2Int(s) + (if b == '1' { 1 } else { 0 })
{
    // By definition of Str2Int on (s + [b]):
    // Str2Int(s + [b]) = 2 * Str2Int((s + [b]).subrange(0, len-1)) + bit_last
    // and here (s + [b]).subrange(0, len-1) == s and bit_last == b.
    if (s.len() == 0) {
        // length of s + [b] is 1
        assert((s + seq![b]).len() as int - 1 == 0);
    } else {
        // length of s + [b] is s.len() + 1
        assert((s + seq![b]).len() as int - 1 == s.len() as int);
    }
    // last element is b
    assert((s + seq![b]).index((s + seq![b]).len() as int - 1) == b);
    // subrange equals s
    assert((s + seq![b]).subrange(0, (s + seq![b]).len() as int - 1) == s);
    // unfold definition
    assert(Str2Int(s + seq![b]) ==
           2 * Str2Int((s + seq![b]).subrange(0, (s + seq![b]).len() as int - 1))
           + (if (s + seq![b]).index((s + seq![b]).len() as int - 1) == '1' { 1 } else { 0 }));
    // combine equalities
    assert(Str2Int(s + seq![b]) == 2 * Str2Int(s) + (if b == '1' { 1 } else { 0 }));
}

exec fn nat_to_vec(n: nat) -> Vec<char>
  ensures Str2Int(result@) == n
  ensures ValidBitString(result@)
  decreases n
{
    if n == 0 {
        return Vec::<char>::new();
    } else {
        let mut v = nat_to_vec(n / 2);
        // capture old sequence for reasoning
        let old_seq = v@;
        let bit = if n % 2 == 1 { '1' } else { '0' };
        v.push(bit);
        // prove correctness: v@ == old_seq + [bit], so Str2Int(v@) == 2*Str2Int(old_seq) + bitval
        proof {
            lemma_str_append(old_seq, bit);
            // by recursive postcondition Str2Int(old_seq) == n/2
            assert(Str2Int(old_seq) == n / 2);
            // from lemma: Str2Int(old_seq + [bit]) == 2*Str2Int(old_seq) + ...
            assert(Str2Int(v@) == 2 * Str2Int(old_seq) + (if bit == '1' { 1 } else { 0 }));
            // arithmetic: 2*(n/2) + bitval == n
            assert(2 * (n / 2) + (if bit == '1' { 1 } else { 0 }) == n);
            assert(Str2Int(v@) == n);
        }
        // ValidBitString: recursive postcondition gives old_seq valid, pushing '0'/'1' preserves validity
        assert(ValidBitString(v@));
        return v;
    }
}

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    // compute numeric values of s1 and s2
    let mut i: usize = 0;
    let mut a: nat = 0;
    while i < s1.len()
        invariant i <= s1.len()
        invariant a == Str2Int(s1@.subrange(0, i as int))
    {
        let c = s1[i];
        a = 2 * a + (if c == '1' { 1 } else { 0 });
        i += 1;
    }

    let mut j: usize = 0;
    let mut b: nat = 0;
    while j < s2.len()
        invariant j <= s2.len()
        invariant b == Str2Int(s2@.subrange(0, j as int))
    {
        let c = s2[j];
        b = 2 * b + (if c == '1' { 1 } else { 0 });
        j += 1;
    }

    let prod: nat = a * b;
    // convert numeric product to vector of bits (MSB-first, matching Str2Int convention)
    nat_to_vec(prod)
}
// </vc-code>

fn main() {}
}