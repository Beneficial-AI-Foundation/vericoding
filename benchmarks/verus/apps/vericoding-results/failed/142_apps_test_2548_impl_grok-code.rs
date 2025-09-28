// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(digits: Seq<int>) -> bool {
    digits.len() >= 1 && forall|i: int| 0 <= i < digits.len() ==> #[trigger] digits[i] >= 0 && #[trigger] digits[i] <= 9
}

spec fn is_good_subarray(digits: Seq<int>, start: int, end: int) -> bool
    recommends 0 <= start <= end < digits.len()
{
    let subarray_sum = sum(digits.subrange(start, end + 1));
    let subarray_length = end - start + 1;
    subarray_sum == subarray_length
}

spec fn sum(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum(s.drop_first()) }
}

spec fn count_good_subarrays(digits: Seq<int>) -> int
    recommends valid_input(digits)
{
    count_good_subarrays_helper(digits, 0, map![0 => 1], 0, 0)
}

spec fn count_good_subarrays_helper(digits: Seq<int>, pos: int, freq_map: Map<int, int>, 
                                  current_sum: int, current_count: int) -> int
    recommends 
        0 <= pos <= digits.len() &&
        valid_input(digits) &&
        current_count == pos &&
        current_sum >= 0 &&
        (forall|k: int| freq_map.dom().contains(k) ==> #[trigger] freq_map[k] >= 0) &&
        (freq_map.dom().contains(0) ==> freq_map[0] >= 1)
    decreases digits.len() - pos
{
    if pos >= digits.len() { 0 }
    else {
        let new_sum = current_sum + digits[pos];
        let new_count = current_count + 1;
        let diff = new_count - new_sum;
        let contribution = if freq_map.dom().contains(diff) { freq_map[diff] } else { 0 };
        let new_freq_map = freq_map.insert(diff, if freq_map.dom().contains(diff) { freq_map[diff] + 1 } else { 1 });
        contribution + count_good_subarrays_helper(digits, pos + 1, new_freq_map, new_sum, new_count)
    }
}
// </vc-preamble>

// <vc-helpers>
fn count_good_subarrays_helper(digits: Seq<i32>, pos: i32, freq_map: Map<i32, i32>, current_sum: i32, current_count: i32) -> i32
    recommends 
        0 <= pos <= digits.len() as i32 &&
        valid_input(digits) &&
        current_count == pos &&
        current_sum >= 0 &&
        (forall|k: i32| freq_map.dom().contains(k) ==> #[trigger] freq_map[k] >= 0) &&
        (freq_map.dom().contains(0) ==> freq_map[0] >= 1)
    decreases (digits.len() as i32) - pos
{
    if pos >= digits.len() as i32 { 0 }
    else {
        let new_sum = current_sum + digits[pos as int];
        let new_count = current_count + 1;
        let diff = new_count - new_sum;
        let contribution = if freq_map.dom().contains(diff) { freq_map[diff] } else { 0 };
        let new_freq_map = freq_map.insert(diff, if freq_map.dom().contains(diff) { freq_map[diff] + 1 } else { 1 });
        contribution + count_good_subarrays_helper(digits, pos + 1, new_freq_map, new_sum, new_count)
    }
}
// </vc-helpers>

// <vc-spec>
fn count_good_subarrays_in_array(digits: Vec<i8>) -> (count: i8)
    requires 
        valid_input(digits@.map(|i, x| x as int)),
    ensures 
        count >= 0,
        count as int == count_good_subarrays(digits@.map(|i, x| x as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Changed exec types from int to i32 for current_sum, current_count, diff, and freq map to allow in exec code, and cast return value */
    let mut count: i64 = 0;
    let tracked mut freq: Map<i32, i32> = Map::tracked_empty().tracked_insert(0, 1);
    let mut current_sum: i32 = 0;
    let mut current_count: i32 = 0;
    let mut pos: usize = 0;
    while pos < digits.len()
        invariant
            0 <= pos <= digits.len(),
            valid_input(digits@.map(|i, x| x as int)),
            current_sum as int == sum(digits@.map(|i, x| x as int).subrange(0, pos as int)),
            current_count == pos as i32,
            (forall|k: i32| freq.dom().contains(k) ==> #[trigger] freq[k] >= 0),
            freq.dom().contains(0'),
            freq[0'] >= 1
        decreases digits.len() - pos
    {
        proof {
            let spec_digits = digits@.map(|i, x| x as int);
            assert(current_sum as int == sum(spec_digits.subrange(0, pos as int)));
        }
        let digit = digits@[pos] as i32;
        current_sum = current_sum + digit;
        current_count = current_count + 1;
        let diff = current_count - current_sum;
        let contribution = if freq.dom().contains(diff) { freq[diff] } else { 0 };
        count = count + contribution as i64;
        freq.tracked_insert(diff, if freq.dom().contains(diff) { freq[diff] + 1 } else { 1 });
        pos = pos + 1;
    }
    count as i8
}
// </vc-code>


}

fn main() {}