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
/* helper modified by LLM (iteration 5): provided actual recursive proofs for power and string properties */
proof fn lemma_longer_string_greater_value(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() > 0,
        s2.len() > 0,
        s1.len() > s2.len(),
        s1.len() > 1 ==> s1[0] != '0',
        s2.len() > 1 ==> s2[0] != '0'
    ensures Str2Int(s1) > Str2Int(s2)
{
    if s1.len() == 1 {
        assert(s2.len() == 0);
        assert(false);
    } else {
        assert(s1[0] == '1');
        lemma_min_value_multi_char(s1);
        lemma_max_value_any_string(s2);
        lemma_power_comparison(s1.len() as nat, s2.len() as nat);
    }
}

proof fn lemma_min_value_multi_char(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 1,
        s[0] == '1'
    ensures Str2Int(s) >= nat_pow(2, (s.len() - 1) as nat)
{
    let all_zeros = s.subrange(1, s.len() as int);
    lemma_all_zeros_value(all_zeros);
    assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat }));
    assert(Str2Int(s) >= 2 * nat_pow(2, (s.len() - 2) as nat));
    assert(nat_pow(2, (s.len() - 1) as nat) == 2 * nat_pow(2, (s.len() - 2) as nat));
}

proof fn lemma_max_value_any_string(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0
    ensures Str2Int(s) < nat_pow(2, s.len() as nat)
{
    if s.len() == 1 {
        assert(Str2Int(s) <= 1);
        assert(nat_pow(2, 1) == 2);
    } else {
        lemma_max_value_any_string(s.subrange(0, s.len() as int - 1));
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s) < 2 * nat_pow(2, (s.len() - 1) as nat) + 1);
        assert(nat_pow(2, s.len() as nat) == 2 * nat_pow(2, (s.len() - 1) as nat));
    }
}

proof fn lemma_power_comparison(len1: nat, len2: nat)
    requires len1 > len2, len2 > 0
    ensures nat_pow(2, (len1 - 1) as nat) > nat_pow(2, len2 as nat) - 1
{
    lemma_power_monotonic((len1 - 1) as nat, len2 as nat);
    assert(nat_pow(2, len2 as nat) >= 1);
}

proof fn lemma_power_monotonic(a: nat, b: nat)
    requires a >= b
    ensures nat_pow(2, a) >= nat_pow(2, b)
{
    if a == b {
        assert(nat_pow(2, a) == nat_pow(2, b));
    } else {
        if b == 0 {
            assert(nat_pow(2, b) == 1);
            assert(nat_pow(2, a) >= 1);
        } else {
            lemma_power_monotonic(a - 1, b - 1);
            assert(nat_pow(2, a) == 2 * nat_pow(2, a - 1));
            assert(nat_pow(2, b) == 2 * nat_pow(2, b - 1));
        }
    }
}

proof fn lemma_all_zeros_value(s: Seq<char>)
    requires ValidBitString(s), forall |i: int| 0 <= i < s.len() ==> s[i] == '0'
    ensures Str2Int(s) == 0
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
    } else {
        lemma_all_zeros_value(s.subrange(0, s.len() as int - 1));
        assert(Str2Int(s) == 2 * 0 + 0);
    }
}

spec fn nat_pow(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 { 1 } else { base * nat_pow(base, (exp - 1) as nat) }
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
/* code modified by LLM (iteration 5): using strengthened lemma that proves strict inequality */
{
    proof {
        lemma_longer_string_greater_value(s1@, s2@);
    }
    return 1;
}
// </vc-code>

fn main() {}
}
