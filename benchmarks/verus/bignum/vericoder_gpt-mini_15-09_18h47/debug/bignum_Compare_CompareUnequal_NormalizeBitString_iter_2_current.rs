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

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): sanitize pushed bits and maintain invariant relating t@ to s@ under ValidBitString(s@) */
  let mut t = Vec::<char>::new();

  // find first '1'
  let mut i: int = 0;
  while i < s.len() as int && s[i as usize] != '1' {
    i += 1;
  }

  if i == s.len() as int {
    // all zeros or empty -> represent as single '0'
    t.push('0');
  } else {
    let mut j: int = i;
    while j < s.len() as int
        invariant
            t@.len() as int == j - i,
            forall |k: int| 0 <= k && k < t@.len() as int ==>
                (if ValidBitString(s@) then t@.index(k) == s@.index(i + k) else (t@.index(k) == '0' || t@.index(k) == '1')),
        decreases s.len() as int - j
    {
      let c = s[j as usize];
      let to_push = if c == '1' { '1' } else if c == '0' { '0' } else { '0' };
      t.push(to_push);
      j += 1;
    }
  }

  proof {
    if ValidBitString(s@) {
      if i == s.len() as int {
        // s is all zeros -> prove it and equality of Str2Int
        assert(forall |k: int| 0 <= k && k < s@.len() as int ==> s@.index(k) == '0');
        allzeros_str2int_zero(s@);
        assert(Str2Int(s@) == 0);
        assert(t@.len() == 1);
        assert(t@.index(0) == '0');
        assert(Str2Int(t@) == 0);
        assert(Str2Int(s@) == Str2Int(t@));
      } else {
        // by the loop invariant (which under ValidBitString(s@) equates elements), t@ equals the suffix
        assert(t@.len() as int == s@.len() as int - i);
        assert(forall |k: int| 0 <= k && k < t@.len() as int ==> t@.index(k) == s@.index(i + k));
        assert(t@ == s@.subrange(i, s@.len()));
        let suffix = s@.subrange(i, s@.len());
        trim_preserves_str2int(s@.subrange(0, i), suffix);
        assert(Str2Int(s@) == Str2Int(suffix));
        assert(Str2Int(s@) == Str2Int(t@));
      }
    }
  }

  t
}
// </vc-code>

// <vc-spec>
exec fn CompareUnequal(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
   s1@.len() > 0,
   (s1@.len() > 1 ==> s1@[0] != '0'),
   s2@.len() > 0,
   (s2@.len() > 1 ==> s2@[0] != '0'),
   s1@.len() > s2@.len(),
  ensures Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): prove numeric inequality when lengths differ and return 1 */
  proof {
    // Use lemmas: normalized length lower bound for s1 and upper bound for s2
    normalized_len_lb(s1@);
    upper_bound(s2@);
    // s1@.len() > s2@.len(), so pow2(s2.len) <= pow2(s1.len - 1)
    pow2_nondec(s2@.len() as nat, (s1@.len() - 1) as nat);
    assert(Str2Int(s1@) >= pow2((s1@.len() - 1) as nat));
    assert(Str2Int(s2@) < pow2(s2@.len() as nat));
    assert(pow2(s2@.len() as nat) <= pow2((s1@.len() - 1) as nat));
    assert(Str2Int(s2@) < Str2Int(s1@));
  }
  1
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 2): binary exponentiation spec */
spec fn pow2(n: nat) -> nat {
    if n == 0 { 1 } else { 2 * pow2(n - 1) }
}

/* helper modified by LLM (iteration 2): predicate for all zeros */
spec fn IsAllZeros(s: Seq<char>) -> bool {
    forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0'
}

/* helper modified by LLM (iteration 2): removing zero prefix preserves integer value */
proof fn trim_preserves_str2int(prefix: Seq<char>, suffix: Seq<char>)
    requires
        ValidBitString(prefix + suffix),
        IsAllZeros(prefix),
    ensures
        Str2Int(prefix + suffix) == Str2Int(suffix),
    decreases
        prefix.len()
{
    if prefix.len() == 0 {
        // trivial
    } else {
        trim_preserves_str2int(prefix.subrange(1, prefix.len()), suffix);
    }
}

/* helper modified by LLM (iteration 2): all-zeros bitstring has integer value 0 */
proof fn allzeros_str2int_zero(s: Seq<char>)
    requires
        ValidBitString(s),
        IsAllZeros(s),
    ensures
        Str2Int(s) == 0,
    decreases
        s.len()
{
    if s.len() == 0 {
        // Str2Int(empty) == 0 by definition
    } else {
        let s0 = s.subrange(0, s.len() - 1);
        allzeros_str2int_zero(s0);
        // Str2Int(s) = 2 * Str2Int(s0) + 0 = 0
    }
}

/* helper modified by LLM (iteration 2): upper bound of bitstring is < 2^len */
proof fn upper_bound(s: Seq<char>)
    requires
        ValidBitString(s),
    ensures
        Str2Int(s) < pow2(s.len() as nat),
    decreases
        s.len()
{
    if s.len() == 0 {
        // Str2Int(empty) == 0 < 1
    } else {
        let s0 = s.subrange(0, s.len() - 1);
        upper_bound(s0);
        // Str2Int(s) = 2 * Str2Int(s0) + bit <= 2*(pow2(len-1)-1) + 1 < pow2(len)
    }
}

/* helper modified by LLM (iteration 2): monotonicity of pow2 */
proof fn pow2_nondec(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow2(a) <= pow2(b),
    decreases
        b - a
{
    if a == b {
    } else {
        pow2_nondec(a, b - 1);
        assert(pow2(b - 1) <= pow2(b));
    }
}

/* helper modified by LLM (iteration 2): normalized string lower bound based on length */
proof fn normalized_len_lb(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0,
        (s.len() > 1 ==> s.index(0) != '0'),
    ensures
        (s.len() > 1 ==> Str2Int(s) >= pow2((s.len() - 1) as nat)),
    decreases
        s.len()
{
    if s.len() <= 1 {
        // if len == 1 and bit is '1' then equality holds; no-op otherwise
    } else {
        // head == '1' by precondition, tail has length one less
        let tail = s.subrange(0, s.len() - 1);
        normalized_len_lb(tail);
        // Str2Int(s) = 2 * Str2Int(tail) + lastbit >= 2 * pow2((s.len() - 2) as nat) = pow2((s.len() - 1) as nat)
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
  /* code modified by LLM (iteration 2): normalize inputs then compare by length or recursively by prefix */
  let t1 = NormalizeBitString(s1);
  let t2 = NormalizeBitString(s2);
  let t1s = t1.as_slice();
  let t2s = t2.as_slice();

  // If lengths differ, decide by CompareUnequal (or its negation)
  if t1s.len() > t2s.len() {
    return CompareUnequal(t1s, t2s);
  }
  if t1s.len() < t2s.len() {
    let r = CompareUnequal(t2s, t1s);
    return -r;
  }

  // Equal lengths: compare recursively by prefixes
  if t1s.len() == 0 {
    return 0;
  }

  let len = t1s.len();
  let prefix1 = t1s[0..len - 1].to_vec();
  let prefix2 = t2s[0..len - 1].to_vec();
  let res_prefix = Compare(prefix1.as_slice(), prefix2.as_slice());
  if res_prefix != 0 {
    return res_prefix;
  }

  // prefixes equal numerically; compare least significant bits
  let last1 = t1s[len - 1];
  let last2 = t2s[len - 1];
  if last1 == last2 {
    return 0;
  }
  if last1 == '0' {
    return -1;
  } else {
    return 1;
  }

  proof {
    // NormalizeBitString preserves integer value when inputs are valid
    if ValidBitString(s1@) {
      assert(Str2Int(s1@) == Str2Int(t1@));
    }
    if ValidBitString(s2@) {
      assert(Str2Int(s2@) == Str2Int(t2@));
    }
    // The rest follows by case analysis above and recursion
  }
}

// </vc-code>

fn main() {}
}


