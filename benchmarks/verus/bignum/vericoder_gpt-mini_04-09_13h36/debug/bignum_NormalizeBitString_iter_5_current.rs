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
proof fn lemma_drop_leading_zero(s: Seq<char>)
  requires ValidBitString(s)
  requires s.len() > 0
  requires s.index(0) == '0'
  ensures Str2Int(s) == Str2Int(s.subrange(1, s.len()))
  decreases s.len()
{
    if s.len() == 1 {
        // Str2Int of single '0' is 0, and empty is 0
        assert(Str2Int(s) == 0nat);
        assert(Str2Int(s.subrange(1, s.len())) == 0nat);
    } else {
        let n = s.len();
        // ensure recursive call preconditions for the prefix r = s.subrange(0, n-1)
        assert(ValidBitString(s.subrange(0, n - 1)));
        assert(s.subrange(0, n - 1).len() > 0);
        // first element of subrange equals original first element
        assert(s.subrange(0, n - 1).index(0) == s.index(0));
        assert(s.subrange(0, n - 1).index(0) == '0');
        lemma_drop_leading_zero(s.subrange(0, n - 1));
        // Unfold definitions for s and s.subrange(1,n)
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, n - 1)) + (if s.index(n - 1) == '1' { 1nat } else { 0nat }));
        // For s.subrange(1,n), its length is n-1 > 0, so expand its definition similarly.
        assert(Str2Int(s.subrange(1, n)) == 2 * Str2Int(s.subrange(1, n - 1)) + (if s.index(n - 1) == '1' { 1nat } else { 0nat }));
        // By induction on the prefix we have equality of the inner Str2Int
        assert(Str2Int(s.subrange(0, n - 1)) == Str2Int(s.subrange(1, n - 1)));
        // hence the two expressions are equal
        assert(2 * Str2Int(s.subrange(0, n - 1)) + (if s.index(n - 1) == '1' { 1nat } else { 0nat })
               == 2 * Str2Int(s.subrange(1, n - 1)) + (if s.index(n - 1) == '1' { 1nat } else { 0nat }));
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
        // k > 0, so s.index(0) == '0' holds from precondition
        assert(k > 0);
        assert(s.index(0) == '0');
        assert(s.len() > 0);
        lemma_drop_leading_zero(s);
        // prepare to apply lemma to the rest
        let s1 = s.subrange(1, s.len());
        assert(ValidBitString(s1));
        // show the prefix-of-length-(k-1) of s1 is all zeros
        assert(0 <= k - 1 && k - 1 <= s1.len());
        // for any i < k-1, s1.index(i) == s.index(i+1) and i+1 < k => s.index(i+1) == '0'
        assert(forall |i: int| 0 <= i && i < k - 1 ==>
            s1.index(i) == '0');
        lemma_drop_prefix_zeros(s1, k - 1);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    let n_usize = s.len();
    let n: int = n_usize as int;

    // First pass: validate that s contains only '0' or '1'
    let mut i: int = 0;
    let mut ok: bool = true;
    while i < n
        invariant 0 <= i && i <= n
        invariant ok ==> (forall |j: int| 0 <= j && j < i ==> (s@.index(j) == '0' || s@.index(j) == '1'))
        decreases n - i
    {
        let c = s[i as usize];
        if c != '0' && c != '1' {
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
    // Second pass: find first '1'
    let mut first_one: int = 0;
    while first_one < n && s@.index(first_one) != '1'
        invariant 0 <= first_one && first_one <= n
        invariant forall |j: int| 0 <= j && j < first_one ==> s@.index(j) == '0'
        decreases n - first_one
    {
        first_one = first_one + 1;
    }

    if first_one == n {
        // All zeros -> return single '0'
        let mut t = Vec::<char>::new();
        t.push('0');
        proof {
            // All positions < n are '0'
            lemma_drop_prefix_zeros(s@, n);
            // Str2Int(s@) == Str2Int(s@.subrange(n, n)) == 0
            assert(Str2Int(s@) == Str2Int(s@.subrange(n, n)));
            assert(Str2Int(s@.subrange(n, n)) == 0nat);
            // Str2Int of single '0' is 0 as well
            assert(Str2Int(Seq::<char>::from_slice(&['0']).@) == 0nat);
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
        decreases n - j
    {
        let cc = s[j as usize];
        t.push(cc);
        j = j + 1;
    }

    // Now t@ == s@.subrange(first_one, n), and ValidBitString(t@) holds
    proof {
        lemma_drop_prefix_zeros(s@, first_one);
        assert(Str2Int(s@) == Str2Int(s@.subrange(first_one, n)));
        assert(t@ == s@.subrange(first_one, n));
        assert(Str2Int(s@) == Str2Int(t@));
    }

    return t;
}
// </vc-code>

fn main() {}
}