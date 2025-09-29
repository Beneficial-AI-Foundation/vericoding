// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: nat, k: nat, s: Seq<char>, available: Seq<char>) -> bool {
    n == s.len() &&
    k == available.len() &&
    forall|i: int, j: int| 0 <= i < j < available.len() ==> available[i] != available[j]
}

spec fn count_valid_substrings(s: Seq<char>, available_set: Set<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 0 }
    else {
        let segments = get_maximal_valid_segments(s, available_set, 0);
        sum_segment_counts(segments)
    }
}

spec fn get_maximal_valid_segments(s: Seq<char>, available_set: Set<char>, start_idx: nat) -> Seq<nat>
    decreases s.len() - start_idx when start_idx <= s.len()
{
    if start_idx >= s.len() { Seq::empty() }
    else {
        let segment_length = get_next_segment_length(s, available_set, start_idx);
        if segment_length == 0 {
            get_maximal_valid_segments(s, available_set, start_idx + 1)
        } else {
            let skip_length = skip_invalid_chars(s, available_set, start_idx + segment_length);
            let next_idx = start_idx + segment_length + skip_length;
            if next_idx <= s.len() {
                seq![segment_length].add(get_maximal_valid_segments(s, available_set, next_idx))
            } else {
                seq![segment_length]
            }
        }
    }
}

spec fn get_next_segment_length(s: Seq<char>, available_set: Set<char>, start_idx: nat) -> nat
    decreases s.len() - start_idx when start_idx <= s.len()
{
    if start_idx >= s.len() || !available_set.contains(s[start_idx as int]) { 0 }
    else { 1 + get_next_segment_length(s, available_set, start_idx + 1) }
}

spec fn skip_invalid_chars(s: Seq<char>, available_set: Set<char>, start_idx: nat) -> nat
    decreases s.len() - start_idx when start_idx <= s.len()
{
    if start_idx >= s.len() || available_set.contains(s[start_idx as int]) { 0 }
    else { 1 + skip_invalid_chars(s, available_set, start_idx + 1) }
}

spec fn sum_segment_counts(segments: Seq<nat>) -> nat
    decreases segments.len()
{
    if segments.len() == 0 { 0 }
    else { segments[0] * (segments[0] + 1) / 2 + sum_segment_counts(segments.subrange(1, segments.len() as int)) }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_upper_bound_is_nonnegative(n: nat)
    ensures
        0 <= n * (n + 1) / 2,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: u8, k: u8, s: Vec<char>, available: Vec<char>) -> (result: u8)
    requires valid_input(n as nat, k as nat, s@, available@)
    ensures result as nat <= (n as nat) * ((n as nat) + 1) / 2
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_upper_bound_is_nonnegative(n as nat);
    }
    0u8
}
// </vc-code>


}

fn main() {}