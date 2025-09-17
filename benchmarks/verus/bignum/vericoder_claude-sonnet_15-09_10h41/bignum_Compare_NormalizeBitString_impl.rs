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
/* helper modified by LLM (iteration 5): fixed proof logic for bit comparison and value monotonicity */
proof fn str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        exists |i: int| 0 <= i < s1.len() && s1.index(i) == '0' && s2.index(i) == '1' && forall |j: int| 0 <= j < i ==> s1.index(j) == s2.index(j),
    ensures
        Str2Int(s1) < Str2Int(s2),
    decreases s1.len(),
{
    let i = choose |i: int| 0 <= i < s1.len() && s1.index(i) == '0' && s2.index(i) == '1' && forall |j: int| 0 <= j < i ==> s1.index(j) == s2.index(j);
    if s1.len() == 0 {
        assert(false);
    } else if i == s1.len() - 1 {
        let prefix1 = s1.subrange(0, i);
        let prefix2 = s2.subrange(0, i);
        assert(Str2Int(prefix1) == Str2Int(prefix2));
    } else {
        let prefix1 = s1.subrange(0, i);
        let prefix2 = s2.subrange(0, i);
        let mid1 = s1.subrange(i, i + 1);
        let mid2 = s2.subrange(i, i + 1);
        let suffix1 = s1.subrange(i + 1, s1.len() as int);
        let suffix2 = s2.subrange(i + 1, s2.len() as int);
        assert(Str2Int(prefix1) == Str2Int(prefix2));
    }
}

proof fn str2int_equal(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1 == s2,
    ensures
        Str2Int(s1) == Str2Int(s2),
    decreases s1.len(),
{
}

proof fn str2int_length_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() < s2.len(),
        s2.len() > 0,
        exists |k: int| 0 <= k < s2.len() && s2.index(k) == '1',
    ensures
        Str2Int(s1) < Str2Int(s2),
    decreases s1.len() + s2.len(),
{
    if s1.len() == 0 {
        assert(Str2Int(s1) == 0);
        assert(Str2Int(s2) >= 1);
    } else {
        assert(Str2Int(s1) < pow2(s1.len() as nat));
        assert(Str2Int(s2) >= 1);
        if s1.len() < s2.len() {
            pow2_monotonic(s1.len() as nat, (s2.len() - 1) as nat);
        }
    }
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn pow2_monotonic(a: nat, b: nat)
    requires a <= b,
    ensures pow2(a) <= pow2(b),
    decreases b,
{
    if a == b {
    } else if a < b {
        pow2_monotonic(a, (b - 1) as nat);
    }
}

proof fn bit_diff_implies_str2int_diff(s1: Seq<char>, s2: Seq<char>, i: int)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        0 <= i < s1.len(),
        s1.index(i) == '0',
        s2.index(i) == '1',
        forall |j: int| 0 <= j < i ==> s1.index(j) == s2.index(j),
    ensures
        Str2Int(s1) < Str2Int(s2),
    decreases s1.len(),
{
    str2int_monotonic(s1, s2);
}
// </vc-helpers>

// <vc-spec>
exec fn Compare(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1,
  decreases Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed loop invariants and precondition checking */
    if s1.len() < s2.len() {
        if s2.len() > 0 {
            let mut has_one = false;
            let mut j = 0;
            while j < s2.len()
                invariant
                    0 <= j <= s2.len(),
                    has_one == exists |k: int| 0 <= k < j && s2@.index(k) == '1',
                decreases s2.len() - j,
            {
                if s2[j] == '1' {
                    has_one = true;
                }
                j += 1;
            }
            if has_one {
                proof {
                    str2int_length_monotonic(s1@, s2@);
                }
            }
        }
        return -1;
    } else if s1.len() > s2.len() {
        if s1.len() > 0 {
            let mut has_one = false;
            let mut j = 0;
            while j < s1.len()
                invariant
                    0 <= j <= s1.len(),
                    has_one == exists |k: int| 0 <= k < j && s1@.index(k) == '1',
                decreases s1.len() - j,
            {
                if s1[j] == '1' {
                    has_one = true;
                }
                j += 1;
            }
        }
        return 1;
    } else {
        let mut i = 0;
        while i < s1.len()
            invariant
                0 <= i <= s1.len(),
                s1.len() == s2.len(),
                forall |j: int| 0 <= j < i ==> s1@.index(j) == s2@.index(j),
            decreases s1.len() - i,
        {
            if s1[i] < s2[i] {
                proof {
                    bit_diff_implies_str2int_diff(s1@, s2@, i as int);
                }
                return -1;
            } else if s1[i] > s2[i] {
                return 1;
            }
            i += 1;
        }
        proof {
            str2int_equal(s1@, s2@);
        }
        return 0;
    }
}
// </vc-code>

fn main() {}
}


