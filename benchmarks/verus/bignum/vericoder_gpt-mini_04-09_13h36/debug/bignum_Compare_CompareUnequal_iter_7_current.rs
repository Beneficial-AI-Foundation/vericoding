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
proof fn pow2(n: nat) -> nat
  decreases n
{
    if n == 0 {
        1
    } else {
        2 * pow2(n - 1)
    }
}

proof fn Str2Int_all_zero(s: Seq<char>)
  requires forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0'
  ensures Str2Int(s) == 0
  decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
    } else {
        let n = s.len();
        let s0 = s.subrange(0, n as int - 1);
        // last char is '0' by requires
        Str2Int_all_zero(s0);
        assert(Str2Int(s) == 2 * Str2Int(s0) + (if s.index(n as int - 1) == '1' { 1 } else { 0 }));
        assert(s.index(n as int - 1) == '0');
        assert(Str2Int(s) == 2 * Str2Int(s0));
        assert(Str2Int(s0) == 0);
        assert(Str2Int(s) == 0);
    }
}

proof fn Str2Int_concat(u: Seq<char>, v: Seq<char>)
  ensures Str2Int(u + v) == pow2(v.len()) * Str2Int(u) + Str2Int(v)
  decreases v.len()
{
    if v.len() == 0 {
        // v == []
        assert(u + v == u);
        assert(Str2Int(u + v) == Str2Int(u));
        assert(pow2(0) == 1);
        assert(1 * Str2Int(u) + Str2Int(v) == Str2Int(u) + 0);
        assert(Str2Int(u + v) == pow2(0) * Str2Int(u) + Str2Int(v));
    } else {
        let m = v.len();
        let last = v.index(m as int - 1);
        let v0 = v.subrange(0, m as int - 1);
        // (u + v).subrange(0, (u+v).len()-1) == u + v0
        Str2Int_concat(u, v0);
        // By definition of Str2Int:
        assert(Str2Int(u + v) == 2 * Str2Int(u + v0)
               + (if last == '1' { 1 } else { 0 }));
        // By IH:
        assert(Str2Int(u + v0) == pow2(v0.len()) * Str2Int(u) + Str2Int(v0));
        // Algebra:
        assert(2 * Str2Int(u + v0) ==
               2 * (pow2(v0.len()) * Str2Int(u) + Str2Int(v0)));
        assert(2 * pow2(v0.len()) == pow2(v.len()));
        assert(2 * Str2Int(v0) + (if last == '1' { 1 } else { 0 })
               == Str2Int(v));
        assert(Str2Int(u + v) ==
               pow2(v.len()) * Str2Int(u) + Str2Int(v));
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
  let n = s.len() as int;
  // find if any invalid char exists, and first index of '1'
  let mut i: int = 0;
  let mut first_one: int = -1;
  let mut invalid: bool = false;
  while i < n
    decreases (n - i);
    invariant 0 <= i && i <= n;
    invariant forall |k: int| 0 <= k && k < i ==> (s@.index(k) == '0' || s@.index(k) == '1');
    invariant first_one >= -1 && first_one <= i;
    invariant first_one != -1 ==> (0 <= first_one && first_one < n && s@.index(first_one) == '1');
    invariant forall |k: int| 0 <= k && k < first_one ==> s@.index(k) == '0';
  {
    let c = s[i];
    if !(c == '0' || c == '1') {
      invalid = true;
    } else {
      if first_one == -1 && c == '1' {
        first_one = i;
      }
    }
    i += 1;
  }

  if invalid {
    let mut t = Vec::<char>::new();
    t.push('0');
    return t;
  }

  if first_one == -1 {
    // All characters are '0' (or n == 0). Return single '0'.
    let mut t = Vec::<char>::new();
    t.push('0');
    return t;
  }

  // Copy suffix starting at first_one ..
  let mut t = Vec::<char>::new();
  let mut j: int = first_one;
  while j < n
    decreases (n - j);
    invariant first_one <= j && j <= n;
    invariant t@.len() == ((j - first_one) as nat);
    invariant forall |k: int| 0 <= k && k < t@.len() as int ==> (t@.index(k) == '0' || t@.index(k) == '1');
    invariant forall |k: int| 0 <= k && k < t@.len() as int ==> t@.index(k) == s@.index(first_one + k);
  {
    t.push(s[j]);
    j += 1;
  }

  proof {
    // From the scanning loop invariants and invalid == false we have that s@ is a valid bitstring.
    assert(forall |k: int| 0 <= k && k < n ==> (s@.index(k) == '0' || s@.index(k) == '1'));
    // first_one >= 0 here
    assert(first_one >= 0);
    let ss = s@;
    let rest = ss.subrange(first_one, n);
    let zeros = ss.subrange(0, first_one);
    // s equals zeros + rest
    assert(ss == zeros + rest);
    // By construction, t@ equals rest
    // From the copying loop invariants we have t@.len() == (n - first_one) and for each k, t@.index(k) == ss.index(first_one + k)
    assert(t@.len() == (n - first_one) as nat);
    assert(forall |k: int| 0 <= k && k < t@.len() as int ==> t@.index(k) == ss.index(first_one + k));
    // Hence t@ == rest
    assert(t@ == rest);
    // Prove zeros is all zeros to use Str2Int_all_zero
    assert(zeros.len() as int == first_one);
    assert(forall |i: int| 0 <= i && i < zeros.len() as int ==> zeros.index(i) == '0');
    // Now use helper lemmas to show Str2Int(ss) == Str2Int(rest)
    Str2Int_all_zero(zeros);
    Str2Int_concat(zeros, rest);
    // Str2Int(zeros + rest) == pow2(rest.len()) * Str2Int(zeros) + Str2Int(rest)
    assert(Str2Int(ss) == pow2(rest.len()) * Str2Int(zeros) + Str2Int(rest));
    // Str2Int(zeros) == 0
    assert(Str2Int(zeros) == 0);
    // hence Str2Int(ss) == Str2Int(rest)
    assert(Str2Int(ss) == Str2Int(rest));
    // and t@ == rest, so equality holds
    assert(Str2Int(ss) == Str2Int(t@));
  }

  return t;
}
// </vc-code>

fn main() {}
}