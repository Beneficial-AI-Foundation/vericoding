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
spec fn pow2(n: nat) -> nat {
    if n == 0 { 1 } else { 2 * pow2(n - 1) }
}

proof fn lemma_valid_subrange(s: Seq<char>, i: int, j: int)
    requires
        0 <= i,
        i <= j,
        j <= s.len() as int,
        ValidBitString(s),
    ensures
        ValidBitString(s.subrange(i, j)),
{
    assert forall |k: int|
        0 <= k && k < j - i ==> (s.subrange(i, j).index(k) == '0' || s.subrange(i, j).index(k) == '1')
    by
    {
        assert(0 <= i + k && i + k < j);
        assert(0 <= i + k && i + k < s.len() as int);
        assert(s.index(i + k) == '0' || s.index(i + k) == '1');
        assert(s.subrange(i, j).index(k) == s.index(i + k));
    };
}

proof fn lemma_upper_bound_leq(s: Seq<char>)
    requires
        ValidBitString(s),
    ensures
        Str2Int(s) <= pow2(s.len() as nat) - 1,
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
        assert(pow2(0) == 1);
    } else {
        let n_i = s.len() as int;
        let n = s.len() as nat;
        let prefix = s.subrange(0, n_i - 1);
        lemma_valid_subrange(s, 0, n_i - 1);
        lemma_upper_bound_leq(prefix);
        let bit: nat = if s.index(n_i - 1) == '1' { 1nat } else { 0nat };
        assert(bit <= 1nat);
        assert(Str2Int(s) == 2 * Str2Int(prefix) + bit);
        assert(Str2Int(prefix) <= pow2(n - 1) - 1);
        assert(2 * Str2Int(prefix) <= 2 * (pow2(n - 1) - 1));
        assert(2 * (pow2(n - 1) - 1) + bit <= 2 * (pow2(n - 1) - 1) + 1);
        assert(2 * (pow2(n - 1) - 1) + 1 == 2 * pow2(n - 1) - 1);
        assert(pow2(n) == 2 * pow2(n - 1));
        assert(2 * pow2(n - 1) - 1 == pow2(n) - 1);
        assert(Str2Int(s) <= pow2(n) - 1);
    }
}

proof fn lemma_lower_bound_first_bit_one(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0,
        s.index(0) == '1',
    ensures
        Str2Int(s) >= pow2(s.len() as nat - 1),
    decreases s.len()
{
    let n_i = s.len() as int;
    if n_i == 1 {
        assert(Str2Int(s) == if s.index(0) == '1' { 1nat } else { 0nat });
        assert(pow2(0) == 1);
        assert(Str2Int(s) >= pow2(0));
    } else {
        let n = s.len() as nat;
        let prefix = s.subrange(0, n_i - 1);
        lemma_valid_subrange(s, 0, n_i - 1);
        assert(prefix.len() > 0);
        assert(prefix.index(0) == s.index(0));
        lemma_lower_bound_first_bit_one(prefix);
        assert(Str2Int(prefix) >= pow2((n - 1) - 1));
        assert(Str2Int(s) == 2 * Str2Int(prefix) + (if s.index(n_i - 1) == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s) >= 2 * Str2Int(prefix));
        assert(2 * Str2Int(prefix) >= 2 * pow2(n - 2));
        assert(2 * pow2(n - 2) == pow2(n - 1));
    }
}

proof fn lemma_pow2_mono_le(m: nat, n: nat)
    requires
        m <= n,
    ensures
        pow2(m) <= pow2(n),
    decreases n - m
{
    if m == n {
    } else {
        lemma_pow2_mono_le(m, n - 1);
        assert(pow2(n) == 2 * pow2(n - 1));
        assert(2 * pow2(n - 1) >= pow2(n - 1));
        assert(pow2(n - 1) <= pow2(n));
    }
}

proof fn lemma_len_implies_greater(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() > 0,
        s2.len() > 0,
        s1.len() > s2.len(),
        (s1.len() > 1 ==> s1.index(0) != '0'),
        (s2.len() > 1 ==> s2.index(0) != '0'),
    ensures
        Str2Int(s1) > Str2Int(s2),
{
    let n1 = s1.len() as nat;
    let n2 = s2.len() as nat;
    assert(n1 > n2);
    assert(n2 >= 1);
    assert(n1 >= 2);
    assert(s1.index(0) == '0' || s1.index(0) == '1');
    assert(s1.index(0) == '1');
    lemma_lower_bound_first_bit_one(s1);
    lemma_upper_bound_leq(s2);
    assert(Str2Int(s2) <= pow2(n2) - 1);
    assert(pow2(n2) - 1 < pow2(n2));
    assert(Str2Int(s2) < pow2(n2));
    assert(n1 >= n2 + 1);
    assert(n1 - 1 >= n2);
    lemma_pow2_mono_le(n2, n1 - 1);
    assert(pow2(n2) <= pow2(n1 - 1));
    assert(Str2Int(s1) >= pow2(n1 - 1));
    assert(Str2Int(s1) >= pow2(n2));
    assert(Str2Int(s2) < pow2(n2));
    assert(Str2Int(s1) > Str2Int(s2));
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
        lemma_len_implies_greater(s1@, s2@);
    }
    1
}
// </vc-code>

fn main() {}
}
