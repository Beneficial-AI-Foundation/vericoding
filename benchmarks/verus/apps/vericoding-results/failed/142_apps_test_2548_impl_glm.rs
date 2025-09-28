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
/* helper modified by LLM (iteration 5): fix MapView to Map in convert_map */
spec fn convert_map(m: Map<i64, i64>) -> Map<int, int> {
    Map::new(|k: int| {
        let k64 = k as i64;
        if m.dom().contains(k64) {
            Some(m[k64] as int)
        } else {
            None
        }
    })
}

fn count_good_subarrays_helper_exec(
    digits: Vec<i8>,
    pos: usize,
    freq_map: vstd::map::Map<i64, i64>,
    current_sum: i64,
    current_count: i64,
) -> (count: i64)
    requires 
        pos <= digits.len() &&
        valid_input(digits@.map(|i, x| x as int)) &&
        current_count == pos as i64 &&
        current_sum >= 0 &&
        (forall|k: int| freq_map.dom().contains(k as i64) ==> #[trigger] freq_map[k as i64] >= 0) &&
        (freq_map.dom().contains(0) ==> freq_map[0] >= 1)
    ensures 
        count >= 0,
        count as int == count_good_subarrays_helper(
            digits@.map(|i, x| x as int), 
            pos as int, 
            convert_map(freq_map@),
            current_sum as int, 
            current_count as int
        )
    decreases digits.len() - pos
{
    if pos >= digits.len() {
        0
    } else {
        let digit = digits[pos] as i64;
        let new_sum = current_sum + digit;
        let new_count = current_count + 1;
        let diff = new_count - new_sum;
        let contribution = freq_map.get(diff).unwrap_or(0);
        let new_value = freq_map.get(diff).unwrap_or(0) + 1;
        let new_freq_map = freq_map.insert(diff, new_value);
        let recursive_result = count_good_subarrays_helper_exec(digits, pos + 1, new_freq_map, new_sum, new_count);
        let total = contribution + recursive_result;
        total
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
/* code modified by LLM (iteration 5): fix initial map creation to use i64 */
{
    let initial_freq_map = vstd::map::Map::empty();
    let initial_freq_map = initial_freq_map.insert(0 as i64, 1 as i64);
    let result = count_good_subarrays_helper_exec(digits, 0, initial_freq_map, 0, 0);
    result as i8
}
// </vc-code>


}

fn main() {}