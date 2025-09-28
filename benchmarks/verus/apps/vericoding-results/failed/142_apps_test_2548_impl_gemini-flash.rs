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
    /* code modified by LLM (iteration 5): Cast `i` to `int` when used in arithmetic operations with `int`s */
    let n = digits.len();
    if n == 0 { return 0; }

    let mut freq_map: Map<int, int> = Map::empty();
    freq_map = freq_map.insert(0, 1);

    let mut current_sum: int = 0;
    let mut total_count: int = 0;

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            current_sum == sum(digits@.map(|j, x| x as int).subrange(0, i as int)),
            total_count >= 0,
            (forall|k: int| 0 <= k < i ==> #[trigger] digits@[k] as int >= 0 && #[trigger] digits@[k] as int <= 9),
            (forall|key: int| freq_map.dom().contains(key) ==> freq_map[key] >= 0),
            (freq_map.dom().contains(0) ==> freq_map[0] >= 1),
            current_sum >= 0,
            valid_input(digits@.map(|j, x| x as int))
        decreases n - i
    {
        current_sum = current_sum + digits@[i as int] as int;
        let diff = (i as int + 1) - current_sum;

        if freq_map.dom().contains(diff) {
            total_count = total_count + freq_map[diff];
            let new_count = freq_map[diff] + 1;
            freq_map = freq_map.insert(diff, new_count);
        } else {
            freq_map = freq_map.insert(diff, 1);
        }

        i = i + 1;
    }
    total_count as i8
}
// </vc-code>


}

fn main() {}