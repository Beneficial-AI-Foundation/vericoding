// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_a(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0 as int
    } else {
        (if s[0] == 'a' { 1 as int } else { 0 as int }) + count_a(s.subrange(1, s.len() as int))
    }
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 1 && exists|i: int| 0 <= i < s.len() && s[i] == 'a'
}

spec fn is_good_string(s: Seq<char>) -> bool {
    s.len() > 0 && count_a(s) > s.len() as int / 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes required */
proof fn lemma_count_a_subrange(s: Seq<char>, i: int)
    requires
        0 <= i,
        i <= s.len(),
    ensures
        count_a(s) == count_a(s.subrange(0, i)) + count_a(s.subrange(i, s.len())),
    decreases s.len()
{
    if i == 0 {
        assert(count_a(s.subrange(0,0)) == 0);
        assert(count_a(s.subrange(0, s.len())) == count_a(s));
    } else if i == s.len() {
        assert(count_a(s.subrange(s.len(), s.len())) == 0);
        assert(count_a(s.subrange(0, s.len())) == count_a(s));
    } else {
        if s.len() > 0 {
            lemma_count_a_subrange(s.subrange(1, s.len()), i - 1);
        }
    }
}

proof fn lemma_count_a_monotonic(s: Seq<char>, s_prime: Seq<char>)
    requires
        s_prime.len() < s.len(),
        s_prime == s.subrange(0, s_prime.len()),
    ensures
        count_a(s_prime) <= count_a(s),
    decreases s_prime.len()
{
    if s_prime.len() == 0 {
        assert(count_a(s_prime) == 0);
    } else {
        lemma_count_a_monotonic(s.subrange(1,s.len()), s_prime.subrange(1, s_prime.len()));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: usize)
    requires 
        valid_input(s@),
    ensures 
        result >= 1,
        result <= s.len(),
        result == min(2 * count_a(s@) - 1, s.len() as int) as usize,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed mismatched closing delimiters for max spec function */
{
    let s_vec = s;
    let s = s_vec@;

    let mut k: usize = 1;
    let mut max_a_count: int = 0;
    let mut min_len_of_max_a_count: nat = 0;

    while k <= s.len()
        invariant
            1 <= k,
            k <= s.len() + 1,
            // max_a_count is the maximum 'a' count found in any good substring of length <= k-1
            // OR it's 0 if no good substring of length <= k-1 exists (i.e. length 0 or 1)
            max_a_count == (if k == 1 { 0 } else {
                max(|idx: int, len: int| count_a(s.subrange(idx, idx + len))
                where 0 <= idx < s.len() && 1 <= len && len < k && idx + len <= s.len() &&
                count_a(s.subrange(idx, idx + len)) * 2 > len 
                overall)
            }) as int,
            // min_len_of_max_a_count is the minimum length among substrings that achieve max_a_count
            (k == 1 ==> min_len_of_max_a_count == 0),
            (k > 1 && max_a_count > 0 ==> 
                exists|idx: int, len: int| 0 <= idx < s.len() && 1 <= len && len < k && idx + len <= s.len() &&
                count_a(s.subrange(idx, idx + len)) == max_a_count &&
                len == min_len_of_max_a_count
            ),
            (k > 1 && max_a_count == 0 ==> min_len_of_max_a_count == 0),
    {
        let mut i: usize = 0;
        while i + k <= s.len()
            invariant
                1 <= k,
                k <= s.len(),
                0 <= i,
                i <= s.len() - k,
                // max_a_count and min_len_of_max_a_count maintained for lengths < k and indices < i with length k
                max_a_count == (if k == 1 { 0 } else {
                    max(|idx: int, len: int| count_a(s.subrange(idx, idx + len))
                    where (0 <= idx < s.len() && 1 <= len && len < k && idx + len <= s.len()) ||
                          (0 <= idx && idx < i && len == k && idx + len <= s.len())
                    overall)
                }) as int,
                (k == 1 ==> min_len_of_max_a_count == 0),
                (k > 1 && max_a_count > 0 ==> 
                    exists|idx: int, len: int| 
                        ((0 <= idx < s.len() && 1 <= len && len < k && idx + len <= s.len()) ||
                         (0 <= idx && idx < i && len == k && idx + len <= s.len())) &&
                        count_a(s.subrange(idx, idx + len)) == max_a_count &&
                        len == min_len_of_max_a_count
                ),
                (k > 1 && max_a_count == 0 ==> min_len_of_max_a_count == 0),
        {
            let sub = s.subrange(i as int, (i + k) as int);
            let current_a_count = count_a(sub);

            if current_a_count as int * 2 > k as int {
                if current_a_count > max_a_count {
                    max_a_count = current_a_count;
                    min_len_of_max_a_count = k as nat;
                } else if current_a_count == max_a_count {
                    if k < min_len_of_max_a_count as usize {
                        min_len_of_max_a_count = k as nat;
                    }
                }
            }
            i = i + 1;
        }
        k = k + 1;
    }

    if max_a_count == 0 {
        // This case implies that no 'good' substring (count_a > len/2) was found
        // This should not happen given the valid_input precondition
        // As valid_input implies there's at least one 'a', the string 'a' itself is good.
        // We handle this case to satisfy requirements of Verus if the above reasoning is not automatically proven.

        // Find the index of the first 'a'
        let mut first_a_idx: usize = 0;
        while first_a_idx < s.len()
            invariant
                0 <= first_a_idx <= s.len(),
                (exists|j: int| 0 <= j < s.len() && s@[j] == 'a') ==> (forall|x: int| 0 <= x < first_a_idx ==> s@[x] != 'a'),
        {
            if s[first_a_idx as int] == 'a' {
                break;
            }
            first_a_idx = first_a_idx + 1;
        }
        assert(first_a_idx < s.len()) by { // Proves that first_a_idx is a valid index
            if (first_a_idx == s.len()) {
                assert(forall|j: int| 0 <= j < s.len() ==> s@[j] != 'a');
                assert(count_a(s) == 0);
                assert(valid_input(s) ==> exists|idx| 0 <= idx < s.len() && s@[idx] == 'a');
                assert(false);
            }
        }
        // The substring of length 1 containing this 'a' is a good string: count_a = 1, len = 1.
        // 1 * 2 > 1. Thus, max_a_count must be at least 1, and min_len_of_max_a_count must be at least 1.
        // Therefore, this branch is unreachable due to the invariant conditions derived from valid_input.
    }

    let expected_result = min(2 * max_a_count - 1, s.len() as int);
    expected_result as usize
}
// </vc-code>


}

fn main() {}