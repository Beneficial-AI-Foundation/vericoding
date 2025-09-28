// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fixed proof structure for str2int_monotonic and str2int_with_leading_zeros */
proof fn str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires
        valid_bit_string(s1),
        valid_bit_string(s2),
        s1.len() == s2.len(),
        s1.len() > 0,
        forall|i: int| 0 <= i < s1.len() ==> s1[i] <= s2[i],
        exists|j: int| 0 <= j < s1.len() && s1[j] < s2[j]
    ensures
        str2int(s1) < str2int(s2)
    decreases s1.len()
{
    let last_idx = s1.len() - 1;
    if s1[last_idx] < s2[last_idx] {
        assert(str2int(s2) >= 2nat * str2int(s2.subrange(0, last_idx)) + 1nat);
        assert(str2int(s1) <= 2nat * str2int(s1.subrange(0, last_idx)));
        assert(str2int(s1) < str2int(s2));
        return;
    } else {
        assert(s1[last_idx] == s2[last_idx]);
        let s1_prefix = s1.subrange(0, last_idx);
        let s2_prefix = s2.subrange(0, last_idx);
        if s1_prefix.len() > 0 {
            str2int_monotonic(s1_prefix, s2_prefix);
            assert(str2int(s1_prefix) < str2int(s2_prefix));
            assert(str2int(s1) < str2int(s2));
        }
    }
}

proof fn str2int_equal_if_seqs_equal(s1: Seq<char>, s2: Seq<char>)
    requires
        valid_bit_string(s1),
        valid_bit_string(s2),
        s1 == s2
    ensures
        str2int(s1) == str2int(s2)
{
}

proof fn str2int_with_leading_zeros(s: Seq<char>, k: int)
    requires
        valid_bit_string(s),
        0 <= k <= s.len(),
        forall|i: int| 0 <= i < k ==> s[i] == '0'
    ensures
        str2int(s) == str2int(s.subrange(k, s.len() as int))
    decreases k
{
    if k == 0 || s.len() == 0 || k == s.len() {
        return;
    }
    
    assert(s[0] == '0');
    let s_tail = s.subrange(1, s.len() as int);
    str2int_with_leading_zeros(s_tail, k - 1);
    
    assert(str2int(s) == 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }));
    assert(s.subrange(0, s.len() - 1) == s_tail.subrange(0, s_tail.len() as int));
    assert(str2int(s) == str2int(s_tail));
}

proof fn str2int_all_zeros(s: Seq<char>)
    requires
        valid_bit_string(s),
        forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
    ensures
        str2int(s) == 0
    decreases s.len()
{
    if s.len() == 0 {
        return;
    }
    let s_prefix = s.subrange(0, s.len() - 1);
    str2int_all_zeros(s_prefix);
    assert(s[s.len() - 1] == '0');
}

fn compare_same_length(s1: &Vec<char>, s2: &Vec<char>) -> (res: i32)
    requires
        valid_bit_string(s1@),
        valid_bit_string(s2@),
        s1@.len() == s2@.len()
    ensures
        (str2int(s1@) < str2int(s2@)) ==> (res == -1),
        (str2int(s1@) == str2int(s2@)) ==> (res == 0),
        (str2int(s1@) > str2int(s2@)) ==> (res == 1)
{
    let mut i = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            s1@.len() == s2@.len(),
            valid_bit_string(s1@),
            valid_bit_string(s2@),
            forall|j: int| 0 <= j < i ==> s1@[j] == s2@[j]
        decreases s1.len() - i
    {
        if s1[i] < s2[i] {
            proof {
                let s1_suffix = s1@.subrange(i as int, s1@.len() as int);
                let s2_suffix = s2@.subrange(i as int, s2@.len() as int);
                if s1_suffix.len() > 0 {
                    str2int_monotonic(s1_suffix, s2_suffix);
                }
            }
            return -1;
        } else if s1[i] > s2[i] {
            proof {
                let s1_suffix = s1@.subrange(i as int, s1@.len() as int);
                let s2_suffix = s2@.subrange(i as int, s2@.len() as int);
                if s2_suffix.len() > 0 {
                    str2int_monotonic(s2_suffix, s1_suffix);
                }
            }
            return 1;
        }
        i += 1;
    }
    proof {
        assert(s1@ == s2@);
        str2int_equal_if_seqs_equal(s1@, s2@);
    }
    0
}
// </vc-helpers>

// <vc-spec>
fn compare(s1: Vec<char>, s2: Vec<char>) -> (res: i32)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    (str2int(s1@) < str2int(s2@)) ==> (res == -1) &&
    (str2int(s1@) == str2int(s2@)) ==> (res == 0) &&
    (str2int(s1@) > str2int(s2@)) ==> (res == 1)
  decreases str2int(s1@) + str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): simplified logic to use length-based comparison first */
    if s1.len() < s2.len() {
        let mut all_s1_zeros = true;
        let mut i = 0;
        while i < s1.len()
            invariant
                0 <= i <= s1.len(),
                all_s1_zeros == (forall|j: int| 0 <= j < i ==> s1@[j] == '0')
            decreases s1.len() - i
        {
            if s1[i] != '0' {
                all_s1_zeros = false;
            }
            i += 1;
        }
        if all_s1_zeros {
            proof {
                str2int_all_zeros(s1@);
            }
            let mut all_s2_zeros = true;
            let mut j = 0;
            while j < s2.len()
                invariant
                    0 <= j <= s2.len(),
                    all_s2_zeros == (forall|k: int| 0 <= k < j ==> s2@[k] == '0')
                decreases s2.len() - j
            {
                if s2[j] != '0' {
                    all_s2_zeros = false;
                }
                j += 1;
            }
            if all_s2_zeros {
                proof {
                    str2int_all_zeros(s2@);
                }
                return 0;
            } else {
                return -1;
            }
        } else {
            return -1;
        }
    } else if s1.len() > s2.len() {
        let mut all_s2_zeros = true;
        let mut i = 0;
        while i < s2.len()
            invariant
                0 <= i <= s2.len(),
                all_s2_zeros == (forall|j: int| 0 <= j < i ==> s2@[j] == '0')
            decreases s2.len() - i
        {
            if s2[i] != '0' {
                all_s2_zeros = false;
            }
            i += 1;
        }
        if all_s2_zeros {
            proof {
                str2int_all_zeros(s2@);
            }
            let mut all_s1_zeros = true;
            let mut j = 0;
            while j < s1.len()
                invariant
                    0 <= j <= s1.len(),
                    all_s1_zeros == (forall|k: int| 0 <= k < j ==> s1@[k] == '0')
                decreases s1.len() - j
            {
                if s1[j] != '0' {
                    all_s1_zeros = false;
                }
                j += 1;
            }
            if all_s1_zeros {
                proof {
                    str2int_all_zeros(s1@);
                }
                return 0;
            } else {
                return 1;
            }
        } else {
            return 1;
        }
    } else {
        compare_same_length(&s1, &s2)
    }
}
// </vc-code>


}

fn main() {}