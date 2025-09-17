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
spec fn map_bit(c: char) -> char {
    if c == '1' { '1' } else { '0' }
}

spec fn is_bit(c: char) -> bool {
    c == '0' || c == '1'
}

proof fn map_preserves_when_valid(c: char)
  ensures is_bit(c) ==> map_bit(c) == c
{
    if c == '1' {
        // map_bit('1') == '1'
    } else {
        // if is_bit(c) then c == '0', and map_bit('0') == '0'
    }
}

proof fn remove_leading_zero_eq(s: Seq<char>)
  ensures
    s.len() as int > 0 && s.index(0) == '0' ==> Str2Int(s) == Str2Int(s.subrange(1, s.len() as int))
  decreases s.len()
{
    if s.len() == 0 {
        // vacuous
    } else if s.len() == 1 {
        if s.index(0) == '0' {
            // Str2Int("0") = 0 = Str2Int("")
            assert(Str2Int(s) == 0);
            assert(Str2Int(s.subrange(1, s.len() as int)) == 0);
        }
    } else {
        // len >= 2
        if s.index(0) == '0' {
            let n = s.len() as int;
            // apply induction on prefix s[0..n-1]
            remove_leading_zero_eq(s.subrange(0, n - 1));
            // unfold definitions of Str2Int to relate values
            assert(Str2Int(s) ==
                2 * Str2Int(s.subrange(0, n - 1))
                + (if s.index(n - 1) == '1' { 1nat } else { 0nat }));
            assert(Str2Int(s.subrange(1, n)) ==
                2 * Str2Int(s.subrange(1, n - 1))
                + (if s.index(n - 1) == '1' { 1nat } else { 0nat }));
            // from induction hypothesis on prefix
            assert(Str2Int(s.subrange(0, n - 1)) == Str2Int(s.subrange(1, n - 1)));
            // conclude equality
            assert(Str2Int(s) == Str2Int(s.subrange(1, n)));
        }
    }
}

proof fn strip_leading_zeros_eq(s: Seq<char>, m: nat)
  requires m <= s.len()
  ensures (forall |i: int| 0 <= i && i < m as int ==> s.index(i) == '0') ==> Str2Int(s) == Str2Int(s.subrange(m as int, s.len() as int))
  decreases m
{
    if m == 0 {
        // trivial: subrange(0, len) equals s
    } else {
        // Prove the implication by case analysis on the antecedent
        if forall |i: int| 0 <= i && i < m as int ==> s.index(i) == '0' {
            // From antecedent we know s.index(0) == '0'
            remove_leading_zero_eq(s);
            // Derive that the subrange starting at 1 has m-1 leading zeros
            assert(forall |i: int| 0 <= i && i < (m - 1) as int ==>
                s.subrange(1, s.len() as int).index(i) == '0');
            // Now apply induction on the remainder
            strip_leading_zeros_eq(s.subrange(1, s.len() as int), m - 1);
            // Combine equalities: Str2Int(s) == Str2Int(s.subrange(1,..)) == Str2Int(s.subrange(m,..))
            assert(Str2Int(s) == Str2Int(s.subrange(m as int, s.len() as int)));
        } else {
            // If antecedent false, implication holds vacuously
        }
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
  let mut t = Vec::<char>::new();

  // Handle empty input: return ["0"]
  if s.len() == 0 {
    t.push('0');
    proof {
      // ValidBitString(t@)
      assert(forall |i: int| 0 <= i && i < t@.len() as int ==>
        (t@.index(i) == '0' || t@.index(i) == '1'));
      // t@.len() > 0
      assert(t@.len() > 0);
      // Str2Int equality when ValidBitString(s@)
      // If s@ is valid, Str2Int(s@) == 0 because s@ empty; Str2Int(t@) == 0 because t = ["0"]
      assert(ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@));
    }
    return t;
  }

  // Find first index p such that s[p] == '1'
  let mut p: usize = 0;
  while p < s.len()
    invariant 0 <= p as int && p as int <= s.len() as int
    invariant forall |k: int| 0 <= k && k < p as int ==> s@.index(k) != '1'
  {
    if s[p] == '1' {
      break;
    }
    p = p + 1;
  }

  if p == s.len() {
    // No '1' found: produce ["0"]
    t.push('0');
    proof {
      // ValidBitString(t@)
      assert(forall |i: int| 0 <= i && i < t@.len() as int ==>
        (t@.index(i) == '0' || t@.index(i) == '1'));
      // t non-empty
      assert(t@.len() > 0);
      // Str2Int: if s is valid then all characters are '0' (no '1'), so Str2Int(s) == 0 == Str2Int(t)
      assert(ValidBitString(s@) ==>
        (forall |i: int| 0 <= i && i < s@.len() as int ==> s@.index(i) == '0'));
      assert(ValidBitString(s@) ==> Str2Int(s@) == 0);
      assert(Str2Int(t@) == 0);
      assert(ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@));
    }
    return t;
  } else {
    // p < s.len(): copy from p to end mapping each char to '0' or '1'
    let mut i: usize = p;
    while i < s.len()
      invariant p <= i && i <= s.len()
      invariant t.len() == i - p
      invariant forall |j: int| 0 <= j && j < t@.len() as int ==>
        t@.index(j) == map_bit(s@.index((p as int) + j))
    {
      // push mapped bit
      let c = if s[i] == '1' { '1' } else { '0' };
      t.push(c);
      i = i + 1;
    }

    proof {
      // Show ValidBitString(t@): all entries are '0' or '1' by construction
      assert(forall |j: int| 0 <= j && j < t@.len() as int ==>
        (t@.index(j) == '0' || t@.index(j) == '1'));

      // t non-empty
      assert(t@.len() > 0);

      // If t.len() > 1 then first element is not '0' because we started at first '1'
      // From loop that found p, for all k < p, s@[k] != '1'. Since p < s.len(), s@[p] == '1'.
      assert(p < s.len());
      assert(s@.index(p as int) == '1');
      // t@[0] is map_bit(s@[p]) which is '1'
      assert(t@.index(0) == map_bit(s@.index(p as int)));
      // map_bit('1') == '1' via proof lemma
      map_preserves_when_valid('1');
      assert(map_bit('1') == '1');
      assert(t@.index(0) == '1');
      // thus if t.len() > 1 then t@[0] != '0'
      assert(t@.len() > 1 ==> t@.index(0) != '0');

      // Finally, Str2Int equality when ValidBitString(s@)
      // If s is a valid bit string, then for all indices before p they are '0' (no '1')
      // so Str2Int(s) == Str2Int(s.subrange(p, s.len()))
      assert(ValidBitString(s@) ==>
        (forall |k: int| 0 <= k && k < p as int ==> s@.index(k) == '0'));
      if ValidBitString(s@) {
        // apply strip_leading_zeros_eq with m = p
        strip_leading_zeros_eq(s@, p as nat);
        // Now show t@ equals s.subrange(p, s.len()) when s is valid: mapping preserves bits
        // For all j < t.len(): t@[j] == map_bit(s@[p+j]) and since s@[p+j] is a bit, map_bit is identity
        assert(forall |j: int| 0 <= j && j < t@.len() as int ==>
          t@.index(j) == map_bit(s@.index((p as int) + j)));
        assert(forall |j: int| 0 <= j && j < t@.len() as int ==>
          is_bit(s@.index((p as int) + j)));
        // From is_bit and lemma, map_bit equals identity for each character
        assert(forall |j: int| 0 <= j && j < t@.len() as int ==>
          map_bit(s@.index((p as int) + j)) == s@.index((p as int) + j));
        // Compose equalities to get t@[j] == s@[p+j]
        assert(forall |j: int| 0 <= j && j < t@.len() as int ==>
          t@.index(j) == s@.index((p as int) + j));
        // Therefore t@ == s.subrange(p, s.len())
        assert(Str2Int(s@) == Str2Int(t@));
      } else {
        // if not ValidBitString(s@), the postcondition about Str2Int equality does not need to hold
        assert(true);
      }
    }

    return t;
  }
}
// </vc-code>

fn main() {}
}