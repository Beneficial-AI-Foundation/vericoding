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
    // By definition of Str2Int on non-empty sequence
    let t = s + seq![b];
    assert(t.index(t.len() as int - 1) == b);
    assert(t.subrange(0, t.len() as int - 1) == s);
    // unfold definition of Str2Int for t
    assert(Str2Int(t) ==
           2 * Str2Int(t.subrange(0, t.len() as int - 1))
           + (if t.index(t.len() as int - 1) == '1' { 1 } else { 0 }));
    assert(Str2Int(t) == 2 * Str2Int(s) + (if b == '1' { 1 } else { 0 }));
}

proof fn lemma_prefix(s: Seq<char>, i: int)
  requires 0 <= i && i < s.len() as int
  ensures Str2Int(s.subrange(0, i + 1)) == 2 * Str2Int(s.subrange(0, i)) + (if s.index(i) == '1' { 1 } else { 0 })
{
    let old = s.subrange(0, i);
    let bit = s.index(i);
    assert(s.subrange(0, i + 1) == old + seq![bit]);
    lemma_str_append(old, bit);
    assert(Str2Int(old + seq![bit]) == 2 * Str2Int(old) + (if bit == '1' { 1 } else { 0 }));
    assert(Str2Int(s.subrange(0, i + 1)) == 2 * Str2Int(old) + (if bit == '1' { 1 } else { 0 }));
}

exec fn nat_to_vec(n: nat) -> (res: Vec<char>)
  ensures Str2Int(res@) == n
  ensures ValidBitString(res@)
  decreases n
{
    if n == 0 {
        let v0 = Vec::<char>::new();
        proof {
            // Str2Int of empty sequence is 0 by definition
            assert(Str2Int(v0@) == 0);
            assert(ValidBitString(v0@));
        }
        return v0;
    } else {
        let mut v = nat_to_vec(n / 2);
        let old_seq = v@;
        let bit = if n % 2 == 1 { '1' } else { '0' };
        v.push(bit);
        proof {
            // By induction and lemma_str_append
            lemma_str_append(old_seq, bit);
            assert(Str2Int(old_seq) == n / 2);
            assert(Str2Int(v@) == 2 * Str2Int(old_seq) + (if bit == '1' { 1 } else { 0 }));
            assert(2 * (n / 2) + (if bit == '1' { 1 } else { 0 }) == n);
            assert(Str2Int(v@) == n);
            assert(ValidBitString(v@));
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
        invariant ValidBitString(s1@.subrange(0, i as int))
    {
        let c = s1[i];
        // update accumulator
        a = 2 * a + (if c == '1' { 1 } else { 0 });
        // prove invariant for i+1
        proof {
            let old = s1@.subrange(0, i as int);
            let bit = s1@.index(i as int);
            assert(bit == c);
            // lemma_prefix requires 0 <= i && i < s.len()
            lemma_prefix(s1@, i as int);
            assert(Str2Int(s1@.subrange(0, i as int + 1)) ==
                   2 * Str2Int(old) + (if bit == '1' { 1 } else { 0 }));
            assert(a == Str2Int(s1@.subrange(0, i as int + 1)));
            assert(ValidBitString(s1@.subrange(0, i as int + 1)));
        }
        i += 1;
    }

    let mut j: usize = 0;
    let mut b: nat = 0;
    while j < s2.len()
        invariant j <= s2.len()
        invariant b == Str2Int(s2@.subrange(0, j as int))
        invariant ValidBitString(s2@.subrange(0, j as int))
    {
        let c = s2[j];
        b = 2 * b + (if c == '1' { 1 } else { 0 });
        proof {
            let old = s2@.subrange(0, j as int);
            let bit = s2@.index(j as int);
            assert(bit == c);
            lemma_prefix(s2@, j as int);
            assert(Str2Int(s2@.subrange(0, j as int + 1)) ==
                   2 * Str2Int(old) + (if bit == '1' { 1 } else { 0 }));
            assert(b == Str2Int(s2@.subrange(0, j as int + 1)));
            assert(ValidBitString(s2@.subrange(0, j as int + 1)));
        }
        j += 1;
    }

    let prod: nat = a * b;
    return nat_to_vec(prod);
}
// </vc-code>

fn main() {}
}