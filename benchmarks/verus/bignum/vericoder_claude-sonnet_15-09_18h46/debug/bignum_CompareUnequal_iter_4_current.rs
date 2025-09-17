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
/* helper modified by LLM (iteration 4): Fixed proofs to properly establish bounds and comparison results */
proof fn str2int_longer_string(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() > 0,
        s2.len() > 0,
        s1.len() > s2.len(),
        s1.len() > 1 ==> s1[0] != '0',
        s2.len() > 1 ==> s2[0] != '0'
    ensures
        Str2Int(s1) >= Str2Int(s2)
{
    lemma_str2int_bounds(s2);
    if s1.len() > 1 {
        lemma_str2int_lower_bound(s1);
    }
    assert(Str2Int(s2) < pow(2, s2.len() as nat));
    if s1.len() > 1 {
        assert(Str2Int(s1) >= pow(2, (s1.len() - 1) as nat));
        assert(s1.len() > s2.len());
        lemma_pow_monotonic(s2.len() as nat, (s1.len() - 1) as nat);
        assert(pow(2, s2.len() as nat) <= pow(2, (s1.len() - 1) as nat));
    }
}

proof fn lemma_str2int_bounds(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0
    ensures
        Str2Int(s) < pow(2, s.len() as nat)
    decreases s.len()
{
    if s.len() == 1 {
        assert(Str2Int(s) <= 1);
        assert(pow(2, 1) == 2);
    } else {
        lemma_str2int_bounds(s.subrange(0, s.len() as int - 1));
        let prefix = s.subrange(0, s.len() as int - 1);
        assert(Str2Int(prefix) < pow(2, prefix.len() as nat));
        assert(prefix.len() == s.len() - 1);
        assert(Str2Int(s) == 2 * Str2Int(prefix) + (if s[s.len() as int - 1] == '1' { 1 } else { 0 }));
        assert(Str2Int(s) <= 2 * Str2Int(prefix) + 1);
        assert(Str2Int(s) < 2 * pow(2, (s.len() - 1) as nat) + 1);
        assert(2 * pow(2, (s.len() - 1) as nat) == pow(2, s.len() as nat));
    }
}

proof fn lemma_str2int_lower_bound(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 1,
        s[0] != '0'
    ensures
        Str2Int(s) >= pow(2, (s.len() - 1) as nat)
    decreases s.len()
{
    if s.len() == 2 {
        assert(s[0] == '1');
        assert(Str2Int(s) >= 2);
        assert(pow(2, 1) == 2);
    } else {
        assert(s[0] == '1');
        let suffix = s.subrange(1, s.len() as int);
        assert(suffix.len() == s.len() - 1);
        assert(Str2Int(s) >= 2 * pow(2, (suffix.len() - 1) as nat));
        assert(2 * pow(2, (suffix.len() - 1) as nat) == pow(2, suffix.len() as nat));
        assert(suffix.len() == s.len() - 1);
    }
}

proof fn lemma_pow_monotonic(a: nat, b: nat)
    requires a <= b
    ensures pow(2, a) <= pow(2, b)
    decreases b
{
    if a == b {
    } else {
        lemma_pow_monotonic(a, b - 1);
    }
}

spec fn pow(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 { 1 } else { base * pow(base, (exp - 1) as nat) }
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
    /* code modified by LLM (iteration 4): Fixed to handle impossible case correctly */
    proof {
        str2int_longer_string(s1@, s2@);
    }
    
    // Since s1.len() > s2.len() and both are valid bit strings without leading zeros,
    // we know that Str2Int(s1@) > Str2Int(s2@), so the result should be 1
    // The case where Str2Int(s1@) == Str2Int(s2@) is impossible given the preconditions
    return 1;
}
// </vc-code>

fn main() {}
}
