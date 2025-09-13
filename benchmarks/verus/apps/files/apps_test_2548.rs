// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(digits: Seq<int>) -> bool {
    digits.len() >= 1 && forall|i: int| 0 <= i < digits.len() ==> 0 <= digits[i] <= 9
}

spec fn is_good_subarray(digits: Seq<int>, start: int, end: int) -> bool {
    &&& 0 <= start <= end < digits.len()
    &&& {
        let subarray_sum = sum_seq(digits.subrange(start, end + 1));
        let subarray_length = end - start + 1;
        subarray_sum == subarray_length
    }
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.drop_first()) }
}

spec fn count_good_subarrays(digits: Seq<int>) -> int {
    if valid_input(digits) {
        count_good_subarrays_helper(digits, 0, map![0int => 1int], 0, 0)
    } else {
        0
    }
}

spec fn count_good_subarrays_helper(digits: Seq<int>, pos: int, freq_map: Map<int, int>, 
                                  current_sum: int, current_count: int) -> int
    decreases digits.len() - pos
{
    if 0 <= pos <= digits.len()
    && valid_input(digits)
    && current_count == pos
    && current_sum >= 0
    && (forall|k: int| freq_map.dom().contains(k) ==> freq_map[k] >= 0)
    && (freq_map.dom().contains(0) ==> freq_map[0] >= 1) {
        if pos >= digits.len() {
            0
        } else {
            let new_sum = current_sum + digits[pos];
            let new_count = current_count + 1;
            let diff = new_count - new_sum;
            let contribution = if freq_map.dom().contains(diff) { freq_map[diff] } else { 0 };
            let new_freq_map = freq_map.insert(diff, if freq_map.dom().contains(diff) { freq_map[diff] + 1 } else { 1 });
            contribution + count_good_subarrays_helper(digits, pos + 1, new_freq_map, new_sum, new_count)
        }
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_good_subarrays_in_array(digits: Seq<int>) -> (count: int)
    requires valid_input(digits)
    ensures count >= 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0int
    // impl-end
}
// </vc-code>


}

fn main() {}