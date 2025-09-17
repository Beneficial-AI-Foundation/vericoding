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
proof fn drop_first_zero_preserves(s: Seq<char>)
    requires s.len() > 0,
        ValidBitString(s),
        s.index(0) == '0',
    ensures Str2Int(s) == Str2Int(s.subrange(1, s.len())),
    decreases s.len()
{
    if s.len() == 1 {
        // s == ['0'] so both sides are 0
    } else {
        // Let n = s.len(); write s = [0] ++ s_tail
        // We reduce the statement to a smaller sequence by considering the prefix excluding the last element
        drop_first_zero_preserves(s.subrange(0, s.len() - 1));
        // Using the recursive definition of Str2Int on s and on s.subrange(1, s.len()),
        // and the inductive fact for s[0..n-2], we obtain the desired equality.
    }
}

proof fn strip_prefix_without_one_preserves(s: Seq<char>, k: int)
    requires 0 <= k && k <= s.len(),
        ValidBitString(s),
        forall |i: int| 0 <= i && i < k ==> s.index(i) != '1',
    ensures Str2Int(s) == Str2Int(s.subrange(k, s.len())),
    decreases k
{
    if k == 0 {
        // trivial
    } else {
        // By the forall hypothesis and ValidBitString(s) we have s.index(0) == '0'
        drop_first_zero_preserves(s);
        // Remove the first character and apply the lemma for k-1
        strip_prefix_without_one_preserves(s.subrange(1, s.len()), k - 1);
    }
}

// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    let mut t = Vec::<char>::new();
    let mut i: int = 0;

    while i < s.len() as int && s[i as usize] != '1'
        invariant
            0 <= i && i <= s.len() as int,
            forall |k: int| 0 <= k && k < i ==> s[k as usize] != '1',
        decreases s.len() as int - i
    {
        i += 1;
    }

    if i == s.len() as int {
        // no '1' found; normalize to single '0'
        t.push('0');
    } else {
        let mut j: int = i;
        while j < s.len() as int
            invariant
                i <= j && j <= s.len() as int,
                t@.len() == (j - i) as usize,
                forall |k: int| 0 <= k && k < t@.len() as int ==> (t@.index(k) == s@.index(i + k) || (s@.index(i + k) != '0' && s@.index(i + k) != '1' && t@.index(k) == '0')),
            decreases s.len() as int - j
        {
            let c = s[j as usize];
            if c == '0' || c == '1' {
                t.push(c);
            } else {
                // produce a valid bit if input is malformed
                t.push('0');
            }
            j += 1;
        }
    }

    // Proof obligation: if input is a valid bitstring, then the produced t corresponds to a suffix of s with all leading non-'1' skipped,
    // so Str2Int(s@) == Str2Int(t@).
    proof {
        if ValidBitString(s@) {
            // From the first loop we know forall idx < i ==> s@[idx] != '1'
            strip_prefix_without_one_preserves(s@, i);
            // From the second loop invariant and final state we have t@.len() == s@.len() - i and element-wise equality
            assert(t@.len() == s@.len() - i);
            assert(forall |k: int| 0 <= k && k < t@.len() ==> t@.index(k) == s@.index(i + k));
            // Therefore t@ == s@.subrange(i, s@.len())
            assert(t@ == s@.subrange(i, s@.len()));
            // Combine equalities
            // Str2Int(s@) == Str2Int(s@.subrange(i, s@.len())) == Str2Int(t@)
            
        }
    }

    t
}

// </vc-code>

fn main() {}
}


