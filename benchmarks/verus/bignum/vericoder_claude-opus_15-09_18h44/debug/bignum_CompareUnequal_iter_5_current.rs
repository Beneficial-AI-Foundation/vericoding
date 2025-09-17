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
/* helper modified by LLM (iteration 5): fixed assertion failures in lemma_str2int_bounds and related lemmas */
proof fn lemma_str2int_bounds(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0
    ensures
        Str2Int(s) >= 0,
        Str2Int(s) < pow2(s.len() as nat)
    decreases s.len()
{
    if s.len() == 1 {
        assert(s[0] == '0' || s[0] == '1');
        if s[0] == '0' {
            reveal(Str2Int);
            assert(Str2Int(s) == 0);
        } else {
            reveal(Str2Int);
            assert(Str2Int(s) == 1);
        }
        reveal(pow2);
        assert(pow2(1nat) == 2);
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        lemma_str2int_bounds(s_prefix);
        assert(Str2Int(s_prefix) < pow2(s_prefix.len() as nat));
        let last_bit = if s[s.len() as int - 1] == '1' { 1nat } else { 0nat };
        assert(Str2Int(s) == 2 * Str2Int(s_prefix) + last_bit);
        assert(Str2Int(s) < 2 * pow2(s_prefix.len() as nat) + 1);
        lemma_pow2_properties(s_prefix.len() as nat);
        assert(2 * pow2(s_prefix.len() as nat) == pow2(s_prefix.len() as nat + 1));
        assert(pow2(s_prefix.len() as nat + 1) == pow2(s.len() as nat));
    }
}

proof fn lemma_pow2_properties(n: nat)
    ensures
        pow2(n + 1) == 2 * pow2(n),
        pow2(0nat) == 1
{
    reveal(pow2);
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn lemma_longer_string_larger(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() > s2.len(),
        s1.len() > 0,
        s2.len() > 0,
        s1.len() > 1 ==> s1[0] != '0',
        s2.len() > 1 ==> s2[0] != '0'
    ensures
        Str2Int(s1) > Str2Int(s2)
{
    lemma_str2int_bounds(s1);
    lemma_str2int_bounds(s2);
    
    if s2.len() == 1 {
        assert(s2[0] == '0' || s2[0] == '1');
        assert(Str2Int(s2) <= 1);
        if s1.len() == 2 {
            assert(s1[0] == '1');
            let s1_prefix = s1.subrange(0, 1);
            assert(s1_prefix[0] == '1');
            reveal(Str2Int);
            assert(Str2Int(s1_prefix) == 1);
            assert(Str2Int(s1) >= 2);
        } else {
            lemma_str2int_min_for_non_zero_prefix(s1);
            assert(Str2Int(s1) >= pow2((s1.len() - 1) as nat));
            lemma_pow2_monotonic(0nat, (s1.len() - 1) as nat);
            assert(pow2((s1.len() - 1) as nat) >= 2);
        }
    } else {
        lemma_str2int_min_for_non_zero_prefix(s1);
        lemma_str2int_max_bound(s2);
        assert(Str2Int(s1) >= pow2((s1.len() - 1) as nat));
        assert(Str2Int(s2) < pow2(s2.len() as nat));
        lemma_pow2_monotonic(s2.len() as nat, (s1.len() - 1) as nat);
    }
}

proof fn lemma_pow2_monotonic(a: nat, b: nat)
    requires a <= b
    ensures pow2(a) <= pow2(b)
    decreases b - a
{
    if a == b {
        assert(pow2(a) == pow2(b));
    } else {
        lemma_pow2_monotonic(a, (b - 1) as nat);
        lemma_pow2_properties((b - 1) as nat);
        assert(pow2(b) == 2 * pow2((b - 1) as nat));
        assert(pow2(a) <= pow2((b - 1) as nat));
        assert(pow2(a) <= pow2(b));
    }
}

proof fn lemma_str2int_min_for_non_zero_prefix(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 1,
        s[0] == '1'
    ensures
        Str2Int(s) >= pow2((s.len() - 1) as nat)
    decreases s.len()
{
    if s.len() == 2 {
        assert(s[0] == '1');
        let s_prefix = s.subrange(0, 1);
        reveal(Str2Int);
        assert(Str2Int(s_prefix) == 1);
        assert(Str2Int(s) >= 2);
        reveal(pow2);
        assert(pow2(1nat) == 2);
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        assert(s_prefix[0] == s[0]);
        lemma_str2int_min_for_non_zero_prefix(s_prefix);
        assert(Str2Int(s_prefix) >= pow2((s_prefix.len() - 1) as nat));
        assert(Str2Int(s) >= 2 * Str2Int(s_prefix));
        assert(Str2Int(s) >= 2 * pow2((s_prefix.len() - 1) as nat));
        lemma_pow2_properties((s_prefix.len() - 1) as nat);
        assert(2 * pow2((s_prefix.len() - 1) as nat) == pow2(s_prefix.len() as nat));
        assert(s_prefix.len() as nat == s.len() as nat - 1);
    }
}

proof fn lemma_str2int_max_bound(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0
    ensures
        Str2Int(s) < pow2(s.len() as nat)
{
    lemma_str2int_bounds(s);
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
/* code modified by LLM (iteration 5): no changes needed to code body */
{
    proof {
        lemma_longer_string_larger(s1@, s2@);
    }
    1
}
// </vc-code>

fn main() {}
}
