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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
proof fn strip_first_zero(s: Seq<char>)
  requires ValidBitString(s) && s.len() > 0 && s.index(0) == '0'
  ensures Str2Int(s) == Str2Int(s.subrange(1, s.len()))
  decreases s.len()
{
    if s.len() == 1 {
        // s == "0"
        assert(s.index(0) == '0');
        assert(Str2Int(s) == 0);
        assert(Str2Int(s.subrange(1, s.len())) == 0);
    } else {
        let n = s.len();
        // Expand definitions
        assert(Str2Int(s) ==
            2 * Str2Int(s.subrange(0, n as int - 1))
            + (if s.index(n as int - 1) == '1' { 1 } else { 0 }));
        assert(Str2Int(s.subrange(1, n)) ==
            2 * Str2Int(s.subrange(1, n as int - 1))
            + (if s.index(n as int - 1) == '1' { 1 } else { 0 }));

        // The prefix s.subrange(0, n-1) also has leading '0' and is ValidBitString
        // so we can apply the lemma recursively to it.
        strip_first_zero(s.subrange(0, n as int - 1));

        // After the recursive call we know:
        assert(Str2Int(s.subrange(0, n as int - 1)) ==
               Str2Int(s.subrange(1, n as int - 1)));

        // Hence the two expanded forms are equal
        assert(2 * Str2Int(s.subrange(0, n as int - 1))
               + (if s.index(n as int - 1) == '1' { 1 } else { 0 })
               ==
               2 * Str2Int(s.subrange(1, n as int - 1))
               + (if s.index(n as int - 1) == '1' { 1 } else { 0 }));

        // Conclude equality
        assert(Str2Int(s) == Str2Int(s.subrange(1, n)));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    // If input is empty, return "0"
    if s.len() == 0 {
        let mut t = Vec::new();
        t.push('0');
        proof {
            assert(ValidBitString(t@));
            assert(t@.len() as int == 1);
            assert(!(t@.len() > 1));
        }
        t
    } else {
        // Find first non-zero character
        let mut start: int = 0;
        while (start < s.len() as int && s[start as usize] == '0')
            invariant 0 <= start && start <= s.len() as int;
            invariant forall |i: int| 0 <= i && i < start ==> s@[i] == '0';
        {
            start += 1;
        }

        if start == s.len() as int {
            // All zeros -> return single '0'
            let mut t = Vec::new();
            t.push('0');

            // If original is valid bitstring, prove Str2Int(s@) == 0 == Str2Int(t@)
            proof {
                if (ValidBitString(s@)) {
                    let n = s.len() as int;
                    // Repeatedly strip first zero until empty
                    let mut j: int = 0;
                    while (j < n)
                        invariant 0 <= j && j <= n;
                    {
                        // current sequence u = s@.subrange(j, n)
                        let u = s@.subrange(j, n);
                        // u.len() > 0 and leading char is '0'
                        assert(u.len() > 0);
                        // from the scanning invariant and start == s.len(), every position < n is '0'
                        assert(s@.index(j) == '0');
                        assert(u.index(0) == '0');
                        strip_first_zero(u);
                        j += 1;
                    }
                    // After removing all chars, Str2Int(s@) == Str2Int(empty) == 0
                    assert(Str2Int(s@) == 0);
                    assert(Str2Int(t@) == 0);
                }
                assert(ValidBitString(t@));
                assert(t@.len() as int == 1);
            }

            t
        } else {
            // Copy s[start..] into t
            let mut t = Vec::new();
            let mut j: int = start;
            // Loop invariant: t@ == s@.subrange(start, j)
            while (j < s.len() as int)
                invariant start <= j && j <= s.len() as int;
                invariant t@.len() as int == j - start;
                invariant t@ == s@.subrange(start, j);
            {
                t.push(s[j as usize]);
                j += 1;
            }
            // After loop, t@ == s@.subrange(start, s.len())
            proof {
                assert(t@ == s@.subrange(start, s.len() as int));
                assert(ValidBitString(t@));
                assert(t@.len() > 0);
                if t@.len() > 1 {
                    // first char is s@[start] and by construction s@[start] != '0'
                    assert(t@[0] == s@[start]);
                    assert(s@[start] != '0');
                }

                // If original s is a valid bitstring, show Str2Int(s@) == Str2Int(t@)
                if (ValidBitString(s@)) {
                    let k = start;
                    let n = s.len() as int;
                    // We will iteratively strip leading zeros k times
                    let mut r: int = 0;
                    // invariant: Str2Int(s@) == Str2Int(s@.subrange(r, n))
                    while (r < k)
                        invariant 0 <= r && r <= k;
                        invariant Str2Int(s@) == Str2Int(s@.subrange(r, n));
                    {
                        let u = s@.subrange(r, n);
                        // Since r < k and k was first non-zero, u.index(0) == '0'
                        assert(u.len() > 0);
                        // from the scanning invariant, positions < k are '0'
                        assert(s@.index(r) == '0');
                        assert(u.index(0) == '0');
                        strip_first_zero(u);
                        r += 1;
                    }
                    // Now r == k, so Str2Int(s@) == Str2Int(s@.subrange(k, n))
                    assert(Str2Int(s@) == Str2Int(s@.subrange(k, n)));
                    // And t@ == s@.subrange(k, n), so conclude equality
                    assert(Str2Int(s@) == Str2Int(t@));
                }
            }

            t
        }
    }
}
// </vc-code>

fn main() {}
}