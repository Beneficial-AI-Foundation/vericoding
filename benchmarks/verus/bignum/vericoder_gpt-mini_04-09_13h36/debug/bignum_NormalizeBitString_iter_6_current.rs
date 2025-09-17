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
        // s == "0"
        assert(Str2Int(s) == 0nat);
        assert(Str2Int(s.subrange(1, s.len())) == 0nat);
    } else {
        let n = s.len();
        // consider prefix r = s.subrange(0, n-1)
        let r = s.subrange(0, n - 1);
        assert(ValidBitString(r));
        assert(r.len() > 0);
        // first element of r equals first of s
        assert(r.index(0) == s.index(0));
        assert(r.index(0) == '0');
        // apply induction to r
        lemma_drop_leading_zero(r);
        // Unfold Str2Int for s and for s.subrange(1,n)
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, n - 1)) + (if s.index(n - 1) == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s.subrange(1, n)) == 2 * Str2Int(s.subrange(1, n - 1)) + (if s.index(n - 1) == '1' { 1nat } else { 0nat }));
        // From induction: Str2Int(r) == Str2Int(r.subrange(1, r.len()))
        assert(Str2Int(s.subrange(0, n - 1)) == Str2Int(s.subrange(1, n - 1)));
        // hence the two expressions equal
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
        // trivial: subrange(0, len) is s
    } else {
        // k > 0
        assert(k > 0);
        assert(s.len() > 0);
        // from precondition, s.index(0) == '0'
        assert(s.index(0) == '0');
        // remove leading zero
        lemma_drop_leading_zero(s);
        // apply lemma to remaining prefix of length k-1 on s1 = s.subrange(1, s.len())
        let s1 = s.subrange(1, s.len());
        assert(ValidBitString(s1));
        // show 0 <= k-1 <= s1.len()
        assert(0 <= k - 1 && k - 1 <= s1.len());
        // show the first k-1 elements of s1 are '0'
        assert(forall |i: int| 0 <= i && i < k - 1 ==> s1.index(i) == '0');
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

    // From the loop: ok == true here. Prove ValidBitString(s@).
    proof {
        assert(ok);
        assert(forall |j: int| 0 <= j && j < n ==> (s@.index(j) == '0' || s@.index(j) == '1'));
        assert(ValidBitString(s@));
    }

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
            // show all positions < n are '0'
            assert(forall |j: int| 0 <= j && j < n ==> s@.index(j) == '0');
            // apply lemma to drop all n zeros
            lemma_drop_prefix_zeros(s@, n);
            assert(Str2Int(s@) == Str2Int(s@.subrange(n, n)));
            assert(Str2Int(s@.subrange(n, n)) == 0nat);
            // Str2Int of single '0' is 0
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

    // Now t@ == s@.subrange(first_one, n), and Str2Int(s@) == Str2Int(t@)
    proof {
        // first_one satisfies: all positions < first_one are '0'
        assert(forall |j0: int| 0 <= j0 && j0 < first_one ==> s@.index(j0) == '0');
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