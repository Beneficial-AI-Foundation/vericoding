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
/* helper modified by LLM (iteration 2): Fixed lemma syntax by removing 'fn' keyword */
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
    if s1.len() == 1 {
        if s2.len() == 1 {
        } else {
        }
    } else {
        lemma_str2int_bounds(s2);
        lemma_str2int_lower_bound(s1);
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
    } else {
        lemma_str2int_bounds(s.subrange(0, s.len() as int - 1));
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
    } else {
        if s[1] != '0' {
            lemma_str2int_lower_bound(s.subrange(1, s.len() as int));
        }
    }
}

spec fn pow(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 { 1 } else { base * pow(base, exp - 1) }
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
    /* code modified by LLM (iteration 2): Fixed compilation error by using correct proof syntax */
    proof {
        str2int_longer_string(s1@, s2@);
    }
    return 1;
}
// </vc-code>

fn main() {}
}
