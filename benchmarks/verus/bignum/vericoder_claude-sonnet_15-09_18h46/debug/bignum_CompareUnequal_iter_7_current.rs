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
/* helper modified by LLM (iteration 7): Fixed pow function assertions and strengthened lemma proofs */
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
        Str2Int(s1) > Str2Int(s2)
{
    lemma_str2int_bounds(s2);
    if s1.len() > 1 {
        lemma_str2int_lower_bound(s1);
        assert(Str2Int(s1) >= pow(2, (s1.len() - 1) as nat));
        assert(Str2Int(s2) < pow(2, s2.len() as nat));
        assert(s1.len() > s2.len());
        assert((s1.len() - 1) as nat >= s2.len() as nat);
        lemma_pow_monotonic(s2.len() as nat, (s1.len() - 1) as nat);
        assert(pow(2, s2.len() as nat) <= pow(2, (s1.len() - 1) as nat));
        assert(Str2Int(s1) >= pow(2, (s1.len() - 1) as nat) >= pow(2, s2.len() as nat) > Str2Int(s2));
    } else {
        // s1.len() == 1, so s1 = "1" (since s1[0] would need to be '1' if s1.len() > 1, but len == 1)
        // s2.len() == 0 is impossible since s2.len() > 0 and s1.len() > s2.len()
        assert(s1.len() == 1);
        assert(s2.len() == 0); // This contradicts s2.len() > 0
        assert(false);
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
        if s[0] == '0' {
            assert(Str2Int(s) == 0nat);
        } else {
            assert(s[0] == '1');
            assert(Str2Int(s) == 1nat);
        }
        lemma_pow_base_case();
        assert(Str2Int(s) < 2nat);
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        lemma_str2int_bounds(prefix);
        assert(Str2Int(prefix) < pow(2, prefix.len() as nat));
        assert(prefix.len() == s.len() - 1);
        let last_bit = if s[s.len() as int - 1] == '1' { 1nat } else { 0nat };
        assert(Str2Int(s) == 2 * Str2Int(prefix) + last_bit);
        assert(last_bit <= 1nat);
        assert(Str2Int(s) <= 2 * Str2Int(prefix) + 1nat);
        assert(Str2Int(s) < 2 * pow(2, (s.len() - 1) as nat) + 1nat);
        lemma_pow_step((s.len() - 1) as nat);
        assert(2 * pow(2, (s.len() - 1) as nat) == pow(2, s.len() as nat));
        assert(Str2Int(s) < pow(2, s.len() as nat));
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
    assert(s[0] == '1');
    if s.len() == 2 {
        // s = "1x" where x is 0 or 1
        if s[1] == '0' {
            assert(Str2Int(s) == 2 * 1nat + 0nat);
            assert(Str2Int(s) == 2nat);
        } else {
            assert(s[1] == '1');
            assert(Str2Int(s) == 2 * 1nat + 1nat);
            assert(Str2Int(s) == 3nat);
        }
        lemma_pow_base_case();
        assert(pow(2, 1nat) == 2nat);
        assert(Str2Int(s) >= 2nat);
    } else {
        // s.len() > 2, s[0] == '1'
        let prefix = s.subrange(0, s.len() as int - 1);
        assert(prefix.len() == s.len() - 1);
        assert(prefix[0] == '1');
        if prefix.len() > 1 {
            lemma_str2int_lower_bound(prefix);
            assert(Str2Int(prefix) >= pow(2, (prefix.len() - 1) as nat));
        } else {
            assert(prefix.len() == 1);
            assert(Str2Int(prefix) == 1nat);
            lemma_pow_base_case();
            assert(pow(2, 0nat) == 1nat);
        }
        let last_bit = if s[s.len() as int - 1] == '1' { 1nat } else { 0nat };
        assert(Str2Int(s) == 2 * Str2Int(prefix) + last_bit);
        assert(Str2Int(s) >= 2 * Str2Int(prefix));
        if prefix.len() > 1 {
            assert(Str2Int(s) >= 2 * pow(2, (prefix.len() - 1) as nat));
            lemma_pow_step((prefix.len() - 1) as nat);
            assert(2 * pow(2, (prefix.len() - 1) as nat) == pow(2, prefix.len() as nat));
            assert(prefix.len() == s.len() - 1);
            assert(Str2Int(s) >= pow(2, (s.len() - 1) as nat));
        } else {
            assert(Str2Int(s) >= 2 * 1nat);
            lemma_pow_base_case();
            assert(pow(2, 1nat) == 2nat);
            assert(s.len() - 1 == 1);
            assert(Str2Int(s) >= pow(2, (s.len() - 1) as nat));
        }
    }
}

proof fn lemma_pow_step(n: nat)
    ensures 2 * pow(2, n) == pow(2, (n + 1) as nat)
{
    // This follows from the definition of pow
}

proof fn lemma_pow_base_case()
    ensures pow(2, 0nat) == 1nat,
        pow(2, 1nat) == 2nat
{
    // Base cases for pow function
}

proof fn lemma_pow_monotonic(a: nat, b: nat)
    requires a <= b
    ensures pow(2, a) <= pow(2, b)
    decreases b
{
    if a == b {
        // trivial
    } else {
        lemma_pow_monotonic(a, (b - 1) as nat);
        assert(pow(2, a) <= pow(2, (b - 1) as nat));
        assert(pow(2, b) == 2 * pow(2, (b - 1) as nat));
        assert(pow(2, a) <= pow(2, b));
    }
}

spec fn pow(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 { 1nat } else { base * pow(base, (exp - 1) as nat) }
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
    /* code modified by LLM (iteration 7): Proved that strings cannot be equal when lengths differ */
    proof {
        str2int_longer_string(s1@, s2@);
        // This proves Str2Int(s1@) > Str2Int(s2@), so equality case is impossible
    }
    
    // Since s1.len() > s2.len() and both are valid bit strings without leading zeros,
    // we have proven that Str2Int(s1@) > Str2Int(s2@), so the result is 1
    return 1;
}
// </vc-code>

fn main() {}
}
