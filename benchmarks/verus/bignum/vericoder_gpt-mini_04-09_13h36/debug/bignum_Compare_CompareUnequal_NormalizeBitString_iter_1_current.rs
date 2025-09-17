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
// <vc-helpers>

spec fn map_bit(c: char) -> char {
    if c == '1' { '1' } else { '0' }
}

spec fn is_bit(c: char) -> bool {
    c == '0' || c == '1'
}

spec fn map_preserves_when_valid(c: char) -> bool
  ensures is_bit(c) ==> map_bit(c) == c
{
    if c == '1' {
        true
    } else {
        // c must be '0' because is_bit(c)
        true
    }
}

spec fn remove_leading_zero_eq(s: Seq<char>) -> bool
  ensures
    s.len() as int > 0 && s.index(0) == '0' ==> Str2Int(s) == Str2Int(s.subrange(1, s.len() as int))
  decreases s.len()
{
    if s.len() == 0 {
        // vacuous
        true
    } else if s.len() == 1 {
        // s = "0"
        if s.index(0) == '0' {
            // Str2Int("0") = 0 = Str2Int("")
            true
        } else {
            // premise false
            true
        }
    } else {
        // len >= 2
        // Str2Int(s) = 2 * Str2Int(s[0..n-1]) + last
        // Str2Int(s.subrange(1,n)) = 2 * Str2Int(s[1..n-1]) + last
        // so suffice to show Str2Int(s[0..n-1]) == Str2Int(s[1..n-1])
        if s.index(0) == '0' {
            // apply induction on s[0..n-1], which has smaller length
            remove_leading_zero_eq(s.subrange(0, s.len() as int - 1))
        } else {
            true
        }
    }
}

spec fn strip_leading_zeros_eq(s: Seq<char>, m: nat) -> bool
  requires m <= s.len()
  requires forall |i: int| 0 <= i && i < m as int ==> s.index(i) == '0'
  ensures Str2Int(s) == Str2Int(s.subrange(m as int, s.len() as int))
  decreases m
{
    if m == 0 {
        true
    } else {
        // m >= 1
        // First show removing one leading zero preserves value, then recurse
        if s.len() == 0 {
            // impossible because m >=1 implies m <= s.len()
            true
        } else {
            // s.index(0) == '0' because forall holds for i=0
            remove_leading_zero_eq(s);
            // now apply recursion on subrange(1, len) with m-1
            strip_leading_zeros_eq(s.subrange(1, s.len() as int), m - 1)
        }
    }
}

// </vc-helpers>
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
      // t@.len() > 1 ==> t@[0] != '0' vacuously true
      // Str2Int equality when ValidBitString(s@)
      // If s@ is valid, Str2Int(s@) == 0 because s@ empty; Str2Int(t@) == 0 because t = ["0"]
      assert(ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@));
    }
    return t;
  }

  // Find first index p such that s[p] == '1'
  let mut p: usize = 0;
  while p < s.len()
    invariant 0 <= p && p <= s.len()
    invariant forall |k: int| 0 <= k && k < p as int ==> s@[k] != '1'
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
        (t@.index(j) == map_bit(s@.index(p as int + j)))
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
      assert(s@[p as int] == '1');
      // t@[0] is map_bit(s@[p]) which is '1'
      assert(t@.index(0) == map_bit(s@.index(p as int)));
      // map_bit('1') == '1'
      assert(map_preserves_when_valid('1'));
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
        strip_leading_zeros_eq(s@, p);
        // Now show t@ equals s.subrange(p, s.len()) when s is valid: mapping preserves bits
        // For all j < t.len(): t@[j] == map_bit(s@[p+j]) and since s@[p+j] is a bit, map_bit is identity
        assert(forall |j: int| 0 <= j && j < t@.len() as int ==>
          t@.index(j) == s@.index(p as int + j));
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