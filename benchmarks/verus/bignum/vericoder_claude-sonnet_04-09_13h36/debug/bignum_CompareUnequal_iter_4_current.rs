use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
spec fn nat_pow(base: nat, exp: nat) -> nat
  decreases exp
{
  if exp == 0 { 1 } else { base * nat_pow(base, (exp - 1) as nat) }
}

proof fn lemma_longer_string_larger_value(s1: Seq<char>, s2: Seq<char>)
  requires ValidBitString(s1), ValidBitString(s2),
    s1.len() > 0, s2.len() > 0,
    s1.len() > s2.len(),
    (s1.len() > 1 ==> s1[0] != '0'),
    (s2.len() > 1 ==> s2[0] != '0')
  ensures Str2Int(s1) > Str2Int(s2)
  decreases s1.len()
{
  if s2.len() == 1 {
    assert(s2[0] == '0' || s2[0] == '1');
    assert(Str2Int(s2) <= 1);
    lemma_min_value_for_length(s1);
    assert(s1.len() > 1);
    assert(Str2Int(s1) >= nat_pow(2, (s1.len() - 1) as nat));
    assert(nat_pow(2, (s1.len() - 1) as nat) >= nat_pow(2, 1));
    lemma_pow_basics();
    assert(nat_pow(2, 1) == 2);
    assert(Str2Int(s1) >= 2 > 1 >= Str2Int(s2));
  } else {
    lemma_min_value_for_length(s1);
    lemma_max_value_for_length(s2);
    assert(Str2Int(s1) >= nat_pow(2, (s1.len() - 1) as nat));
    assert(Str2Int(s2) < nat_pow(2, s2.len() as nat));
    assert((s1.len() - 1) as nat >= s2.len() as nat);
    lemma_pow_monotonic(2, s2.len() as nat, (s1.len() - 1) as nat);
    assert(nat_pow(2, s2.len() as nat) <= nat_pow(2, (s1.len() - 1) as nat));
    assert(Str2Int(s2) < nat_pow(2, s2.len() as nat));
    assert(Str2Int(s1) >= nat_pow(2, (s1.len() - 1) as nat) >= nat_pow(2, s2.len() as nat) > Str2Int(s2));
  }
}

proof fn lemma_min_value_for_length(s: Seq<char>)
  requires ValidBitString(s), s.len() > 0,
    (s.len() > 1 ==> s[0] != '0')
  ensures s.len() == 1 ==> Str2Int(s) >= 0,
    s.len() > 1 ==> Str2Int(s) >= nat_pow(2, (s.len() - 1) as nat)
  decreases s.len()
{
  if s.len() == 1 {
    // Base case
  } else {
    assert(s[0] == '1');
    let prefix = s.subrange(0, s.len() as int - 1);
    assert(prefix.len() > 0);
    assert(prefix[0] == '1');
    if prefix.len() > 1 {
      lemma_min_value_for_length(prefix);
      assert(Str2Int(prefix) >= nat_pow(2, (prefix.len() - 1) as nat));
      assert(Str2Int(s) == 2 * Str2Int(prefix) + (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat }));
      assert(Str2Int(s) >= 2 * nat_pow(2, (prefix.len() - 1) as nat));
      lemma_pow_add_one(2, (prefix.len() - 1) as nat);
    } else {
      assert(prefix.len() == 1);
      assert(prefix[0] == '1');
      assert(Str2Int(prefix) == 1);
      assert(Str2Int(s) >= 2);
      assert(nat_pow(2, (s.len() - 1) as nat) == nat_pow(2, 1));
      lemma_pow_basics();
    }
  }
}

proof fn lemma_max_value_for_length(s: Seq<char>)
  requires ValidBitString(s), s.len() > 0
  ensures Str2Int(s) < nat_pow(2, s.len() as nat)
  decreases s.len()
{
  if s.len() == 1 {
    lemma_pow_basics();
  } else {
    let prefix = s.subrange(0, s.len() as int - 1);
    lemma_max_value_for_length(prefix);
    assert(Str2Int(s) == 2 * Str2Int(prefix) + (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat }));
    assert(Str2Int(s) <= 2 * Str2Int(prefix) + 1);
    assert(Str2Int(s) < 2 * nat_pow(2, prefix.len() as nat) + 1);
    assert(Str2Int(s) <= 2 * nat_pow(2, prefix.len() as nat));
    lemma_pow_add_one(2, prefix.len() as nat);
  }
}

proof fn lemma_pow_basics()
  ensures nat_pow(2, 0) == 1,
    nat_pow(2, 1) == 2,
    nat_pow(2, 2) == 4
{
}

proof fn lemma_pow_add_one(base: nat, exp: nat)
  requires base > 0
  ensures nat_pow(base, exp + 1) == base * nat_pow(base, exp)
{
}

proof fn lemma_pow_monotonic(base: nat, exp1: nat, exp2: nat)
  requires base > 1, exp1 <= exp2
  ensures nat_pow(base, exp1) <= nat_pow(base, exp2)
  decreases exp2
{
  if exp1 == exp2 {
    // Equal case
  } else if exp1 == 0 {
    // Base case
  } else {
    lemma_pow_monotonic(base, exp1 - 1, exp2 - 1);
    lemma_pow_add_one(base, exp1 - 1);
    lemma_pow_add_one(base, exp2 - 1);
  }
}
// </vc-helpers>

// <vc-spec>
exec fn CompareUnequal(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@), ValidBitString(s2@),
    s1@.len() > 0,
    (s1@.len() > 1 ==> s1@[0] != '0'),
    s2@.len() > 0,
    (s2@.len() > 1 ==> s2@[0] != '0'),
    s1@.len() > s2@.len()
  ensures (Str2Int(s1@) < Str2Int(s2@) ==> res == -1),
    (Str2Int(s1@) == Str2Int(s2@) ==> res == 0),
    (Str2Int(s1@) > Str2Int(s2@) ==> res == 1)
// </vc-spec>
// <vc-code>
{
  proof {
    lemma_longer_string_larger_value(s1@, s2@);
  }
  return 1;
}
// </vc-code>

fn main() {}
}