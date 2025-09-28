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
    2nat * str2int(s.subrange(0, s.len() - 1)) + 
    (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn compare_unequal(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
    s1.len() > 0,
    s1.len() > 1 ==> s1[0] != '0',
    s2.len() > 0,
    s2.len() > 1 ==> s2[0] != '0',
    s1.len() > s2.len()
  ensures 
    str2int(s1) < str2int(s2) ==> res == -1,
    str2int(s1) == str2int(s2) ==> res == 0,
    str2int(s1) > str2int(s2) ==> res == 1
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed trigger issue by removing invalid trigger annotation */
proof fn lemma_str2int_empty()
    ensures str2int(Seq::<char>::empty()) == 0nat
{
}

proof fn lemma_str2int_single_zero()
    ensures str2int(seq!['0']) == 0nat
{
    assert(seq!['0'].len() == 1);
    assert(seq!['0'][0] == '0');
    assert(str2int(seq!['0']) == 2nat * str2int(seq!['0'].subrange(0, 0)) + 0nat);
    assert(seq!['0'].subrange(0, 0) == Seq::<char>::empty());
}

proof fn lemma_str2int_single_one()
    ensures str2int(seq!['1']) == 1nat
{
    assert(seq!['1'].len() == 1);
    assert(seq!['1'][0] == '1');
    assert(str2int(seq!['1']) == 2nat * str2int(seq!['1'].subrange(0, 0)) + 1nat);
    assert(seq!['1'].subrange(0, 0) == Seq::<char>::empty());
}

proof fn lemma_str2int_leading_zero(s: Seq<char>)
    requires
        valid_bit_string(s),
        s.len() > 0,
        s[0] == '0'
    ensures
        str2int(s) == str2int(s.subrange(1, s.len() as int))
    decreases s.len()
{
    if s.len() == 1 {
        assert(s == seq!['0']);
        lemma_str2int_single_zero();
        assert(str2int(s) == 0nat);
        assert(s.subrange(1, s.len() as int) == Seq::<char>::empty());
        lemma_str2int_empty();
    } else {
        let last_bit = if s[s.len() - 1] == '1' { 1nat } else { 0nat };
        assert(str2int(s) == 2nat * str2int(s.subrange(0, s.len() - 1)) + last_bit);
        let s_prefix = s.subrange(0, s.len() - 1);
        assert(s_prefix[0] == '0');
        assert(valid_bit_string(s_prefix));
        lemma_str2int_leading_zero(s_prefix);
        assert(str2int(s_prefix) == str2int(s_prefix.subrange(1, s_prefix.len() as int)));
        assert(s.subrange(1, s.len() - 1) == s_prefix.subrange(1, s_prefix.len() as int));
        assert(str2int(s.subrange(1, s.len() as int)) == 2nat * str2int(s.subrange(1, s.len() - 1)) + last_bit);
    }
}

proof fn lemma_str2int_leading_zeros(s: Seq<char>, prefix_len: int)
    requires
        valid_bit_string(s),
        0 <= prefix_len < s.len(),
        forall|j: int| 0 <= j < prefix_len ==> s[j] == '0'
    ensures
        str2int(s) == str2int(s.subrange(prefix_len, s.len() as int))
    decreases prefix_len
{
    if prefix_len == 0 {
        assert(s.subrange(prefix_len, s.len() as int) == s.subrange(0, s.len() as int));
        assert(s.subrange(0, s.len() as int) =~= s);
    } else {
        assert(s[0] == '0');
        lemma_str2int_leading_zero(s);
        assert(str2int(s) == str2int(s.subrange(1, s.len() as int)));
        let s_tail = s.subrange(1, s.len() as int);
        assert(forall|j: int| 0 <= j < prefix_len - 1 ==> s_tail[j] == s[j + 1] && s[j + 1] == '0');
        assert(valid_bit_string(s_tail));
        lemma_str2int_leading_zeros(s_tail, prefix_len - 1);
        assert(str2int(s_tail) == str2int(s_tail.subrange(prefix_len - 1, s_tail.len() as int)));
        assert(s_tail.subrange(prefix_len - 1, s_tail.len() as int) == s.subrange(prefix_len, s.len() as int));
    }
}

fn compare_equal_length(s1: &Vec<char>, s2: &Vec<char>) -> (res: i32)
    requires
        valid_bit_string(s1@),
        valid_bit_string(s2@),
        s1@.len() == s2@.len(),
        s1@.len() > 0
    ensures
        str2int(s1@) < str2int(s2@) ==> res == -1,
        str2int(s1@) == str2int(s2@) ==> res == 0,
        str2int(s1@) > str2int(s2@) ==> res == 1
{
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            s1@.len() == s2@.len(),
            forall|j: int| 0 <= j < i ==> s1@[j] == s2@[j],
            valid_bit_string(s1@),
            valid_bit_string(s2@)
        decreases s1.len() - i
    {
        if s1[i] != s2[i] {
            if s1[i] == '0' {
                assert(s2@[i as int] == '1') by {
                    assert(valid_bit_string(s2@));
                    assert(s2@[i as int] == '0' || s2@[i as int] == '1');
                    assert(s1@[i as int] == '0');
                    assert(s1@[i as int] != s2@[i as int]);
                };
                assert(str2int(s1@) < str2int(s2@));
                return -1;
            } else {
                assert(s1@[i as int] == '1');
                assert(s2@[i as int] == '0');
                assert(str2int(s1@) > str2int(s2@));
                return 1;
            }
        }
        i = i + 1;
    }
    assert(forall|j: int| 0 <= j < s1@.len() ==> s1@[j] == s2@[j]);
    assert(s1@ =~= s2@);
    assert(str2int(s1@) == str2int(s2@));
    0
}
// </vc-helpers>

// <vc-spec>
fn compare(s1: Vec<char>, s2: Vec<char>) -> (res: i32)
  requires valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    str2int(s1@) < str2int(s2@) ==> res == -1,
    str2int(s1@) == str2int(s2@) ==> res == 0,
    str2int(s1@) > str2int(s2@) ==> res == 1
  decreases str2int(s1@) + str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): No changes to main logic */
    
    // Handle empty strings
    if s1.len() == 0 && s2.len() == 0 {
        proof {
            lemma_str2int_empty();
            assert(str2int(s1@) == 0nat);
            assert(str2int(s2@) == 0nat);
        }
        return 0;
    }
    
    if s1.len() == 0 {
        proof {
            lemma_str2int_empty();
            assert(str2int(s1@) == 0nat);
        }
        // Check if s2 represents zero
        let mut all_zeros = true;
        let mut k: usize = 0;
        while k < s2.len()
            invariant
                0 <= k <= s2.len(),
                all_zeros == (forall|j: int| 0 <= j < k ==> s2@[j] == '0'),
                valid_bit_string(s2@)
            decreases s2.len() - k
        {
            if s2[k] != '0' {
                all_zeros = false;
                proof {
                    assert(s2@[k as int] == '1');
                    assert(str2int(s2@) > 0nat);
                }
            }
            k = k + 1;
        }
        if all_zeros {
            proof {
                if s2.len() > 0 {
                    lemma_str2int_leading_zeros(s2@, s2.len() as int - 1);
                }
            }
            return 0;
        } else {
            return -1;
        }
    }
    
    if s2.len() == 0 {
        proof {
            lemma_str2int_empty();
            assert(str2int(s2@) == 0nat);
        }
        // Check if s1 represents zero
        let mut all_zeros = true;
        let mut k: usize = 0;
        while k < s1.len()
            invariant
                0 <= k <= s1.len(),
                all_zeros == (forall|j: int| 0 <= j < k ==> s1@[j] == '0'),
                valid_bit_string(s1@)
            decreases s1.len() - k
        {
            if s1[k] != '0' {
                all_zeros = false;
                proof {
                    assert(s1@[k as int] == '1');
                    assert(str2int(s1@) > 0nat);
                }
            }
            k = k + 1;
        }
        if all_zeros {
            proof {
                if s1.len() > 0 {
                    lemma_str2int_leading_zeros(s1@, s1.len() as int - 1);
                }
            }
            return 0;
        } else {
            return 1;
        }
    }
    
    // Both strings are non-empty
    // Skip leading zeros
    let mut s1_start: usize = 0;
    while s1_start < s1.len() - 1 && s1[s1_start] == '0'
        invariant
            0 <= s1_start < s1.len(),
            forall|j: int| 0 <= j < s1_start ==> s1@[j] == '0',
            valid_bit_string(s1@)
        decreases s1.len() - 1 - s1_start
    {
        s1_start = s1_start + 1;
    }
    
    let mut s2_start: usize = 0;
    while s2_start < s2.len() - 1 && s2[s2_start] == '0'
        invariant
            0 <= s2_start < s2.len(),
            forall|j: int| 0 <= j < s2_start ==> s2@[j] == '0',
            valid_bit_string(s2@)
        decreases s2.len() - 1 - s2_start
    {
        s2_start = s2_start + 1;
    }
    
    let s1_effective_len = s1.len() - s1_start;
    let s2_effective_len = s2.len() - s2_start;
    
    // Compare based on effective length
    if s1_effective_len > s2_effective_len {
        proof {
            if s1_start > 0 {
                assert(valid_bit_string(s1@));
                lemma_str2int_leading_zeros(s1@, s1_start as int);
            }
            if s2_start > 0 {
                assert(valid_bit_string(s2@));
                lemma_str2int_leading_zeros(s2@, s2_start as int);
            }
        }
        return 1;
    } else if s1_effective_len < s2_effective_len {
        proof {
            if s1_start > 0 {
                assert(valid_bit_string(s1@));
                lemma_str2int_leading_zeros(s1@, s1_start as int);
            }
            if s2_start > 0 {
                assert(valid_bit_string(s2@));
                lemma_str2int_leading_zeros(s2@, s2_start as int);
            }
        }
        return -1;
    }
    
    // Same effective length - compare digit by digit
    let mut i: usize = s1_start;
    while i < s1.len()
        invariant
            s1_start <= i <= s1.len(),
            s2_start <= s2_start + (i - s1_start) <= s2.len(),
            s1_effective_len == s2_effective_len,
            s1.len() - s1_start == s2.len() - s2_start,
            forall|j: int| s1_start <= j < i ==> s1@[j] == s2@[s2_start as int + (j - s1_start as int)],
            valid_bit_string(s1@),
            valid_bit_string(s2@)
        decreases s1.len() - i
    {
        let s2_idx = s2_start + (i - s1_start);
        assert(s2_idx < s2.len());
        if s1[i] != s2[s2_idx] {
            if s1[i] == '0' {
                assert(s2@[s2_idx as int] == '1');
                proof {
                    if s1_start > 0 {
                        assert(valid_bit_string(s1@));
                        lemma_str2int_leading_zeros(s1@, s1_start as int);
                    }
                    if s2_start > 0 {
                        assert(valid_bit_string(s2@));
                        lemma_str2int_leading_zeros(s2@, s2_start as int);
                    }
                }
                return -1;
            } else {
                assert(s1@[i as int] == '1');
                assert(s2@[s2_idx as int] == '0');
                proof {
                    if s1_start > 0 {
                        assert(valid_bit_string(s1@));
                        lemma_str2int_leading_zeros(s1@, s1_start as int);
                    }
                    if s2_start > 0 {
                        assert(valid_bit_string(s2@));
                        lemma_str2int_leading_zeros(s2@, s2_start as int);
                    }
                }
                return 1;
            }
        }
        i = i + 1;
    }
    
    proof {
        if s1_start > 0 {
            assert(valid_bit_string(s1@));
            lemma_str2int_leading_zeros(s1@, s1_start as int);
        }
        if s2_start > 0 {
            assert(valid_bit_string(s2@));
            lemma_str2int_leading_zeros(s2@, s2_start as int);
        }
    }
    return 0;
}
// </vc-code>


}

fn main() {}