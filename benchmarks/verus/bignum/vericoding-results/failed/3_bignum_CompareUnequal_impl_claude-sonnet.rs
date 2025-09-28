// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fix proof logic and bounds checking for str2int properties */
proof fn str2int_grows_with_length(s1: Seq<char>, s2: Seq<char>)
    requires
        valid_bit_string(s1),
        valid_bit_string(s2),
        s1.len() > 0,
        s2.len() > 0,
        s1.len() > s2.len(),
        s1.len() > 1 ==> s1[0] != '0',
        s2.len() > 1 ==> s2[0] != '0'
    ensures str2int(s1) > str2int(s2)
    decreases s1.len()
{
    str2int_upper_bound(s2);
    str2int_lower_bound(s1);
    
    assert(str2int(s2) < pow2(s2.len() as nat));
    assert(str2int(s1) >= pow2((s1.len() - 1) as nat));
    
    pow2_monotonic((s2.len() as nat), (s1.len() - 1) as nat);
    assert(pow2(s2.len() as nat) <= pow2((s1.len() - 1) as nat));
    assert(str2int(s2) < pow2((s1.len() - 1) as nat));
    assert(str2int(s1) >= pow2((s1.len() - 1) as nat));
    assert(str2int(s1) > str2int(s2));
}

proof fn str2int_positive_for_nonempty(s: Seq<char>)
    requires
        valid_bit_string(s),
        s.len() > 0,
        s.len() > 1 ==> s[0] != '0'
    ensures str2int(s) >= if s.len() == 1 && s[0] == '0' { 0 } else { 1 }
    decreases s.len()
{
    if s.len() == 1 {
        if s[0] == '1' {
            assert(str2int(s) == 1);
        } else {
            assert(str2int(s) == 0);
        }
    } else {
        assert(s[0] != '0');
        assert(s[0] == '1');
        let prefix = s.subrange(0, s.len() - 1);
        assert(str2int(s) >= 2 * str2int(prefix));
        assert(str2int(s) >= 0);
        assert(str2int(s) >= 1);
    }
}

proof fn str2int_upper_bound(s: Seq<char>)
    requires
        valid_bit_string(s),
        s.len() > 0
    ensures str2int(s) < pow2(s.len() as nat)
    decreases s.len()
{
    if s.len() == 1 {
        pow2_base_case();
        assert(pow2(1) == 2);
        if s[0] == '1' {
            assert(str2int(s) == 1);
        } else {
            assert(str2int(s) == 0);
        }
        assert(str2int(s) < 2);
    } else {
        let prefix = s.subrange(0, s.len() - 1);
        str2int_upper_bound(prefix);
        assert(str2int(prefix) < pow2(prefix.len() as nat));
        assert(str2int(s) <= 2 * str2int(prefix) + 1);
        assert(str2int(s) < 2 * pow2(prefix.len() as nat) + 1);
        pow2_recursive(s.len() as nat);
        assert(pow2(s.len() as nat) == 2 * pow2((s.len() - 1) as nat));
        assert(2 * pow2(prefix.len() as nat) + 1 <= 2 * pow2(prefix.len() as nat));
        assert(str2int(s) < pow2(s.len() as nat));
    }
}

proof fn str2int_lower_bound(s: Seq<char>)
    requires
        valid_bit_string(s),
        s.len() > 0,
        s.len() > 1 ==> s[0] != '0'
    ensures str2int(s) >= if s.len() == 1 && s[0] == '0' { 0 } else { pow2((s.len() - 1) as nat) }
    decreases s.len()
{
    if s.len() == 1 {
        if s[0] == '1' {
            assert(str2int(s) == 1);
            pow2_base_case();
            assert(pow2(0) == 1);
        } else {
            assert(str2int(s) == 0);
        }
    } else {
        assert(s[0] != '0');
        assert(s[0] == '1');
        let prefix = s.subrange(0, s.len() - 1);
        assert(str2int(s) >= 2 * str2int(prefix));
        assert(str2int(prefix) >= 0);
        pow2_recursive(s.len() as nat);
        assert(pow2((s.len() - 1) as nat) == 2 * pow2((s.len() - 2) as nat));
        assert(str2int(s) >= pow2((s.len() - 1) as nat));
    }
}

proof fn pow2_monotonic(a: nat, b: nat)
    requires a <= b
    ensures pow2(a) <= pow2(b)
    decreases b
{
    if a == b {
        assert(pow2(a) == pow2(b));
    } else if a == 0 {
        assert(pow2(a) == 1);
        assert(pow2(b) >= 1);
    } else {
        pow2_monotonic(a - 1, b - 1);
        assert(pow2(a - 1) <= pow2(b - 1));
        assert(pow2(a) == 2 * pow2(a - 1));
        assert(pow2(b) == 2 * pow2(b - 1));
        assert(pow2(a) <= pow2(b));
    }
}

proof fn pow2_base_case()
    ensures pow2(0) == 1 && pow2(1) == 2
{
    assert(pow2(0) == 1);
    assert(pow2(1) == 2 * pow2(0));
    assert(pow2(1) == 2);
}

proof fn pow2_recursive(n: nat)
    requires n > 0
    ensures pow2(n) == 2 * pow2((n - 1) as nat)
{
    assert(pow2(n) == 2 * pow2((n - 1) as nat));
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}
// </vc-helpers>

// <vc-spec>
fn compare_unequal(s1: Vec<char>, s2: Vec<char>) -> (res: i32)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
    s1@.len() > 0,
    s1@.len() > 1 ==> s1@[0] != '0',
    s2@.len() > 0,
    s2@.len() > 1 ==> s2@[0] != '0',
    s1@.len() > s2@.len()
  ensures 
    str2int(s1@) < str2int(s2@) ==> res == -1,
    str2int(s1@) == str2int(s2@) ==> res == 0,
    str2int(s1@) > str2int(s2@) ==> res == 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): use corrected proof functions */
    proof {
        str2int_grows_with_length(s1@, s2@);
        assert(str2int(s1@) > str2int(s2@));
    }
    1
}
// </vc-code>


}

fn main() {}