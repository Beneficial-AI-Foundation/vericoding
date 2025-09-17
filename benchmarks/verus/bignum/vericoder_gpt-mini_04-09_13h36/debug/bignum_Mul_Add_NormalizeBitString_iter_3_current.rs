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
proof fn lemma_str_append(s: Seq<char>, b: char)
  ensures Str2Int(s + seq![b]) == 2 * Str2Int(s) + (if b == '1' { 1 } else { 0 })
{
    // By definition of Str2Int on a non-empty sequence:
    // Str2Int(t) == 2 * Str2Int(t.subrange(0, t.len()-1)) + lastbit
    // for t = s + seq![b], lastbit == b and subrange(0, len-1) == s.
    assert((s + seq![b]).index((s + seq![b]).len() as int - 1) == b);
    assert((s + seq![b]).subrange(0, (s + seq![b]).len() as int - 1) == s);
    assert(Str2Int(s + seq![b]) ==
           2 * Str2Int((s + seq![b]).subrange(0, (s + seq![b]).len() as int - 1))
           + (if (s + seq![b]).index((s + seq![b]).len() as int - 1) == '1' { 1 } else { 0 }));
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
        let old_seq = v@;
        let bit = if n % 2 == 1 { '1' } else { '0' };
        v.push(bit);
        proof {
            lemma_str_append(old_seq, bit);
            assert(Str2Int(old_seq) == n / 2);
            assert(Str2Int(v@) == 2 * Str2Int(old_seq) + (if bit == '1' { 1 } else { 0 }));
            assert(2 * (n / 2) + (if bit == '1' { 1 } else { 0 }) == n);
            assert(Str2Int(v@) == n);
        }
        assert(ValidBitString(v@));
        return v;
    }
}
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
        // update accumulator
        a = 2 * a + (if c == '1' { 1 } else { 0 });
        // prove invariant for i+1
        proof {
            let old = s1@.subrange(0, i as int);
            let bit = s1@.index(i as int);
            assert(bit == c);
            lemma_str_append(old, bit);
            // show Str2Int of prefix of length i+1 equals 2*Str2Int(old) + bitval
            assert(s1@.subrange(0, i as int + 1).len() as int - 1 == i as int);
            assert(s1@.subrange(0, i as int + 1).subrange(0, i as int) == old);
            assert(s1@.subrange(0, i as int + 1).index(i as int) == bit);
            assert(Str2Int(s1@.subrange(0, i as int + 1)) ==
                   2 * Str2Int(old) + (if bit == '1' { 1 } else { 0 }));
            // combine with updated a
            assert(a == Str2Int(s1@.subrange(0, i as int + 1)));
        }
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
        proof {
            let old = s2@.subrange(0, j as int);
            let bit = s2@.index(j as int);
            assert(bit == c);
            lemma_str_append(old, bit);
            assert(s2@.subrange(0, j as int + 1).len() as int - 1 == j as int);
            assert(s2@.subrange(0, j as int + 1).subrange(0, j as int) == old);
            assert(s2@.subrange(0, j as int + 1).index(j as int) == bit);
            assert(Str2Int(s2@.subrange(0, j as int + 1)) ==
                   2 * Str2Int(old) + (if bit == '1' { 1 } else { 0 }));
            assert(b == Str2Int(s2@.subrange(0, j as int + 1)));
        }
        j += 1;
    }

    let prod: nat = a * b;
    return nat_to_vec(prod);
}
// </vc-code>

fn main() {}
}