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
/* helper modified by LLM (iteration 6): power-of-two function */
spec fn pow2(n: nat) -> nat
  decreases n
{
  if n == 0 { 1 } else { 2 * pow2(n - 1) }
}

/* helper modified by LLM (iteration 6): monotonicity of pow2 */
proof fn pow2_monotone(a: nat, b: nat)
  requires a <= b,
  ensures pow2(a) <= pow2(b),
  decreases b - a
{
  if a == b {
    assert(pow2(a) == pow2(b));
  } else {
    assert(b > a);
    if b == 0 {
      // impossible because b > a >= 0
    } else {
      assert(pow2(b) == 2 * pow2(b - 1));
      pow2_monotone(a, b - 1);
      assert(pow2(a) <= pow2(b - 1));
      assert(pow2(b - 1) <= pow2(b));
      assert(pow2(a) <= pow2(b));
    }
  }
}

/* helper modified by LLM (iteration 6): upper bound Str2Int(s) < 2^{len} */
proof fn str2int_upper_bound(s: Seq<char>)
  requires ValidBitString(s),
  ensures Str2Int(s) < pow2(s.len() as nat),
  decreases s.len()
{
  if s.len() == 0 {
    assert(Str2Int(s) == 0);
    assert(0 < pow2(0));
  } else {
    let last = s.index(s.len() as int - 1);
    let prefix = s.subrange(0, s.len() as int - 1);
    str2int_upper_bound(prefix);
    assert(Str2Int(s) == 2 * Str2Int(prefix) + (if last == '1' { 1nat } else { 0nat }));
    assert(Str2Int(prefix) < pow2(prefix.len() as nat));
    assert(2 * Str2Int(prefix) < 2 * pow2(prefix.len() as nat));
    assert(2 * pow2(prefix.len() as nat) == pow2(s.len() as nat));
    assert(2 * Str2Int(prefix) + (if last == '1' { 1nat } else { 0nat }) < pow2(s.len() as nat));
  }
}

/* helper modified by LLM (iteration 6): lower bound when first bit is '1' */
proof fn str2int_lower_bound_nonempty(s: Seq<char>)
  requires ValidBitString(s), s.len() > 0, s.index(0) == '1',
  ensures Str2Int(s) >= pow2((s.len() as nat) - 1),
  decreases s.len()
{
  if s.len() == 1 {
    assert(Str2Int(s) == (if s.index(0) == '1' { 1nat } else { 0nat }));
    assert(Str2Int(s) >= 1);
  } else {
    let last = s.index(s.len() as int - 1);
    let prefix = s.subrange(0, s.len() as int - 1);
    // prefix has same first bit
    assert(prefix.len() + 1 == s.len());
    // prefix.index(0) == '1' because s.index(0) == '1'
    str2int_lower_bound_nonempty(prefix);
    assert(Str2Int(s) == 2 * Str2Int(prefix) + (if last == '1' { 1nat } else { 0nat }));
    assert(Str2Int(prefix) >= pow2((prefix.len() as nat) - 1));
    assert(2 * Str2Int(prefix) >= 2 * pow2((prefix.len() as nat) - 1));
    assert(2 * pow2((prefix.len() as nat) - 1) == pow2((s.len() as nat) - 1));
    assert(2 * Str2Int(prefix) + (if last == '1' { 1nat } else { 0nat }) >= pow2((s.len() as nat) - 1));
  }
}

/* helper modified by LLM (iteration 6): drop single leading zero preserves value */
proof fn drop_leading_zero_preserves(s: Seq<char>)
  requires s.len() > 0, s.index(0) == '0',
  ensures Str2Int(s) == Str2Int(s.subrange(1, s.len() as int)),
  decreases s.len()
{
  if s.len() == 1 {
    assert(Str2Int(s) == 0);
    assert(Str2Int(s.subrange(1, s.len() as int)) == Str2Int(Seq::<char>::empty()));
    assert(Str2Int(Seq::<char>::empty()) == 0);
  } else {
    let last = s.index(s.len() as int - 1);
    let prefix = s.subrange(0, s.len() as int - 1); // starts with '0'
    let t = s.subrange(1, s.len());
    // prefix starts with '0'
    assert(prefix.index(0) == s.index(0));
    drop_leading_zero_preserves(prefix);
    // apply definitions
    assert(Str2Int(s) == 2 * Str2Int(prefix) + (if last == '1' { 1nat } else { 0nat }));
    assert(Str2Int(prefix) == Str2Int(t.subrange(0, t.len() as int - 1)));
    assert(Str2Int(t) == 2 * Str2Int(t.subrange(0, t.len() as int - 1)) + (if last == '1' { 1nat } else { 0nat }));
    assert(Str2Int(s) == Str2Int(t));
  }
}

/* helper modified by LLM (iteration 6): trim p leading zeros preserves value */
proof fn trim_leading_zeros_preserves(s: Seq<char>, p: int)
  requires ValidBitString(s), 0 <= p && p <= s.len() as int, forall |i: int| 0 <= i && i < p ==> s.index(i) == '0',
  ensures Str2Int(s) == Str2Int(s.subrange(p, s.len() as int)),
  decreases p
{
  if p == 0 {
    assert(Str2Int(s) == Str2Int(s));
  } else {
    // first character is '0'
    assert(s.index(0) == '0');
    drop_leading_zero_preserves(s);
    let t = s.subrange(1, s.len());
    trim_leading_zeros_preserves(t, p - 1);
    assert(Str2Int(s) == Str2Int(t));
    assert(Str2Int(t) == Str2Int(t.subrange(p - 1, t.len() as int)));
    assert(Str2Int(s) == Str2Int(s.subrange(p, s.len() as int)));
  }
}

/* helper modified by LLM (iteration 6): lexicographic difference implies numeric difference for equal lengths */
proof fn lexicographic_implies_numeric(s: Seq<char>, t: Seq<char>, k: int)
  requires ValidBitString(s), ValidBitString(t), s.len() == t.len(), 0 <= k && k < s.len() as int,
    forall |i: int| 0 <= i && i < k ==> s.index(i) == t.index(i), s.index(k) == '0' && t.index(k) == '1',
  ensures Str2Int(s) < Str2Int(t),
  decreases s.len()
{
  if k == 0 {
    // MSB differs: s has 0, t has 1
    // Then Str2Int(s) < Str2Int(t) because leading bit contributes pow2(len-1)
    str2int_lower_bound_nonempty(t);
    str2int_upper_bound(s);
    assert(Str2Int(s) < Str2Int(t));
  } else {
    // Reduce to suffixes
    let s1 = s.subrange(1, s.len());
    let t1 = t.subrange(1, t.len());
    // apply induction on k-1 for suffixes
    lexicographic_implies_numeric(s1, t1, k - 1);
    // from s1 < t1 derive s < t
    assert(Str2Int(s1) < Str2Int(t1));
    assert(2 * Str2Int(s1) + 1 <= 2 * Str2Int(t1));
    assert(Str2Int(s) <= 2 * Str2Int(s1) + 1);
    assert(Str2Int(t) >= 2 * Str2Int(t1));
    assert(Str2Int(s) < Str2Int(t));
  }
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
    /* code modified by LLM (iteration 6): compare by skipping leading zeros and lexicographic comparison for equal lengths */
    let n1: usize = s1.len();
    let n2: usize = s2.len();

    let mut p1: usize = 0;
    while p1 < n1
        invariant
            p1 <= n1,
        decreases n1 - p1
    {
        if s1[p1] == '1' {
            break;
        }
        p1 += 1;
    }

    let mut p2: usize = 0;
    while p2 < n2
        invariant
            p2 <= n2,
        decreases n2 - p2
    {
        if s2[p2] == '1' {
            break;
        }
        p2 += 1;
    }

    let eff1: usize = if p1 == n1 { 0 } else { n1 - p1 };
    let eff2: usize = if p2 == n2 { 0 } else { n2 - p2 };

    if eff1 < eff2 {
        proof {
            let ss1 = s1@;
            let ss2 = s2@;
            let p1_i: int = p1 as int;
            let p2_i: int = p2 as int;
            trim_leading_zeros_preserves(ss1, p1_i);
            trim_leading_zeros_preserves(ss2, p2_i);
            let rem1 = ss1.subrange(p1_i, ss1.len());
            let rem2 = ss2.subrange(p2_i, ss2.len());
            assert(rem2.len() as int > 0);
            str2int_upper_bound(rem1);
            str2int_lower_bound_nonempty(rem2);
            assert(Str2Int(ss1) == Str2Int(rem1));
            assert(Str2Int(ss2) == Str2Int(rem2));
            pow2_monotone(eff1 as nat, (eff2 - 1) as nat);
            assert(Str2Int(rem1) < pow2(eff1 as nat));
            assert(pow2(eff1 as nat) <= pow2((eff2 - 1) as nat));
            assert(pow2((eff2 - 1) as nat) <= Str2Int(rem2));
            assert(Str2Int(ss1) < Str2Int(ss2));
        }
        return -1;
    } else if eff1 > eff2 {
        proof {
            let ss1 = s1@;
            let ss2 = s2@;
            let p1_i: int = p1 as int;
            let p2_i: int = p2 as int;
            trim_leading_zeros_preserves(ss1, p1_i);
            trim_leading_zeros_preserves(ss2, p2_i);
            let rem1 = ss1.subrange(p1_i, ss1.len());
            let rem2 = ss2.subrange(p2_i, ss2.len());
            assert(rem1.len() as int > 0);
            str2int_lower_bound_nonempty(rem1);
            str2int_upper_bound(rem2);
            pow2_monotone(eff2 as nat, (eff1 - 1) as nat);
            assert(Str2Int(ss1) == Str2Int(rem1));
            assert(Str2Int(ss2) == Str2Int(rem2));
            assert(Str2Int(rem2) < pow2(eff2 as nat));
            assert(pow2(eff2 as nat) <= pow2((eff1 - 1) as nat));
            assert(pow2((eff1 - 1) as nat) <= Str2Int(rem1));
            assert(Str2Int(ss1) > Str2Int(ss2));
        }
        return 1;
    } else {
        if eff1 == 0 {
            return 0;
        }
        let rem1 = &s1[p1..];
        let rem2 = &s2[p2..];
        let mut k: usize = 0;
        while k < eff1
            invariant
                k <= eff1,
            decreases eff1 - k
        {
            let b1 = rem1[k];
            let b2 = rem2[k];
            if b1 == b2 {
                k += 1;
            } else if b1 == '0' && b2 == '1' {
                proof {
                    let ss1 = s1@;
                    let ss2 = s2@;
                    let p1_i: int = p1 as int;
                    let p2_i: int = p2 as int;
                    let pref1 = ss1.subrange(p1_i, ss1.len());
                    let pref2 = ss2.subrange(p2_i, ss2.len());
                    let k_i: int = k as int;
                    assert(forall |i: int| 0 <= i && i < k_i ==> pref1.index(i) == pref2.index(i));
                    lexicographic_implies_numeric(pref1, pref2, k_i);
                    assert(Str2Int(ss1) == Str2Int(pref1));
                    assert(Str2Int(ss2) == Str2Int(pref2));
                    assert(Str2Int(ss1) < Str2Int(ss2));
                }
                return -1;
            } else {
                proof {
                    let ss1 = s1@;
                    let ss2 = s2@;
                    let p1_i: int = p1 as int;
                    let p2_i: int = p2 as int;
                    let pref1 = ss1.subrange(p1_i, ss1.len());
                    let pref2 = ss2.subrange(p2_i, ss2.len());
                    let k_i: int = k as int;
                    assert(forall |i: int| 0 <= i && i < k_i ==> pref1.index(i) == pref2.index(i));
                    lexicographic_implies_numeric(pref2, pref1, k_i);
                    assert(Str2Int(ss1) > Str2Int(ss2));
                }
                return 1;
            }
        }
        return 0;
    }
}

// </vc-code>

fn main() {}
}


