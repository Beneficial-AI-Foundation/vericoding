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
proof fn lemma_drop_leading_zero(s: Seq<char>)
  requires ValidBitString(s)
  requires s.len() > 0
  requires s.index(0) == '0'
  ensures Str2Int(s) == Str2Int(s.subrange(1, s.len()))
  decreases s.len()
{
    if s.len() == 1 {
        // Str2Int of single '0' is 0, and empty is 0
        assert(Str2Int(s) == 0);
        assert(Str2Int(s.subrange(1, s.len())) == 0);
    } else {
        let n = s.len();
        // r = s.subrange(0, n-1)
        // r has same first char as s
        lemma_drop_leading_zero(s.subrange(0, n - 1));
        // Unfold definitions for s and s.subrange(1,n)
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, n - 1)) + (if s.index(n - 1) == '1' { 1 } else { 0 }));
        assert(Str2Int(s.subrange(1, n)) == 2 * Str2Int(s.subrange(1, n - 1)) + (if s.index(n - 1) == '1' { 1 } else { 0 }));
        // By induction on the prefix r we have equality of the inner Str2Int
        assert(Str2Int(s.subrange(0, n - 1)) == Str2Int(s.subrange(1, n - 1)));
        // hence the two expressions are equal
        assert(2 * Str2Int(s.subrange(0, n - 1)) + (if s.index(n - 1) == '1' { 1 } else { 0 })
               == 2 * Str2Int(s.subrange(1, n - 1)) + (if s.index(n - 1) == '1' { 1 } else { 0 }));
    }
}

proof fn lemma_drop_prefix_zeros(s: Seq<char>, k: int)
  requires ValidBitString(s)
  requires 0 <= k && k <= s.len()
  requires forall |i: int| 0 <= i && i < k ==> s.index(i) == '0'
  ensures Str2Int(s) == Str2Int(s.subrange(k, s.len()))
  decreases k
{
    if k == 0 {
        // trivial
    } else {
        // apply one-step lemma to drop the first zero
        lemma_drop_leading_zero(s);
        // prepare to apply lemma to the rest
        let s1 = s.subrange(1, s.len());
        assert(ValidBitString(s1));
        // show the prefix-of-length-(k-1) of s1 is all zeros
        assert(0 <= k - 1 && k - 1 <= s1.len());
        assert(forall |i: int| 0 <= i && i < k - 1 ==> s1.index(i) == '0');
        lemma_drop_prefix_zeros(s1, k - 1);
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    let n_usize = s.len();
    let n: int = n_usize as int;

    // Scan s to determine if it is a valid bitstring and find first '1'
    let mut i: int = 0;
    let mut first_one: int = n;
    let mut ok: bool = true;
    while i < n
        invariant 0 <= i && i <= n
        invariant 0 <= first_one && first_one <= n
        invariant ok ==> (forall |j: int| 0 <= j && j < i ==> (s@.index(j) == '0' || s@.index(j) == '1'))
        invariant first_one <= i
    {
        let c = s[i as usize];
        if c == '1' {
            if first_one == n {
                first_one = i;
            }
            // continue with ok true
        } else if c == '0' {
            // nothing special
        } else {
            ok = false;
        }
        i = i + 1;
    }

    if !ok {
        // Input not a valid bitstring: return canonical "0"
        let mut t = Vec::<char>::new();
        t.push('0');
        return t;
    }

    // Now s@ is ValidBitString
    // If no '1' was found, the string is all zeros -> return single '0'
    if first_one == n {
        let mut t = Vec::<char>::new();
        t.push('0');
        // prove the postconditions: ValidBitString(t@) and length > 0 hold trivially
        // and Str2Int equality follows from lemma_drop_prefix_zeros with k = n (all zeros)
        proof {
            lemma_drop_prefix_zeros(s@, n);
            // Str2Int(s@) == Str2Int(s@.subrange(n, n)) == Str2Int(Seq::empty())
            assert(Str2Int(s@) == Str2Int(s@.subrange(n, n)));
            assert(Str2Int(s@.subrange(n, n)) == 0);
            assert(Str2Int(Seq::<char>::from_slice(&['0']).@) == 0);
            assert(Str2Int(s@) == Str2Int(Seq::<char>::from_slice(&['0']).@));
        }
        return t;
    }

    // Otherwise, construct t as s[first_one .. n)
    let mut t = Vec::<char>::new();
    let mut j: int = first_one;
    while j < n
        invariant first_one <= j && j <= n
        invariant t@ == s@.subrange(first_one, j)
    {
        let cc = s[j as usize];
        t.push(cc);
        j = j + 1;
    }

    // Now t@ == s@.subrange(first_one, n), and ValidBitString(t@) holds
    proof {
        // From the scan loop we know s@ is valid and prefix zeros up to first_one
        lemma_drop_prefix_zeros(s@, first_one);
        // So Str2Int(s@) == Str2Int(s@.subrange(first_one, n))
        assert(Str2Int(s@) == Str2Int(s@.subrange(first_one, n)));
        // And t@ equals that subrange
        assert(t@ == s@.subrange(first_one, n));
        // therefore Str2Int(s@) == Str2Int(t@)
        assert(Str2Int(s@) == Str2Int(t@));
    }

    // Ensure leading-zero property: because first char of t@ is '1' when length>1
    // (first_one points to first '1' in s)
    return t;
}
// </vc-code>

fn main() {}
}