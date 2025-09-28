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
    /* code modified by LLM (iteration 4): Fixed Ghost initialization syntax */
    let mut pos: usize = 0;
    let mut freq_map = std::collections::HashMap::<i8, i8>::new();
    freq_map.insert(0, 1);
    let mut current_sum: i8 = 0;
    let mut current_count: i8 = 0;
    let mut total: i8 = 0;
    
    let mut ghost_freq_map: Ghost<Map<int, int>> = Ghost(Map::empty().insert(0int, 1));
    
    while pos < digits.len()
        invariant
            0 <= pos <= digits.len(),
            valid_input(digits@.map(|i, x| x as int)),
            current_count == pos as i8,
            current_sum >= 0,
            total >= 0,
            total as int == count_good_subarrays_helper(digits@.map(|i, x| x as int), 0, Map::empty().insert(0int, 1), 0, 0) - count_good_subarrays_helper(digits@.map(|i, x| x as int), pos as int, ghost_freq_map@, current_sum as int, current_count as int),
            forall|k: i8| #[trigger] freq_map.contains_key(&k) ==> freq_map[&k] >= 0,
            freq_map.contains_key(&0) ==> freq_map[&0i8] >= 1,
        decreases digits.len() - pos
    {
        current_sum = current_sum + digits[pos];
        current_count = current_count + 1;
        let diff: i8 = current_count - current_sum;
        
        if freq_map.contains_key(&diff) {
            total = total + freq_map[&diff];
        }
        
        if freq_map.contains_key(&diff) {
            let old_val = freq_map[&diff];
            freq_map.insert(diff, old_val + 1);
        } else {
            freq_map.insert(diff, 1);
        }
        
        proof {
            let new_ghost_map = if ghost_freq_map@.dom().contains(diff as int) {
                ghost_freq_map@.insert(diff as int, ghost_freq_map@[diff as int] + 1)
            } else {
                ghost_freq_map@.insert(diff as int, 1)
            };
            ghost_freq_map = Ghost(new_ghost_map);
        }
        
        pos = pos + 1;
    }
    
    total
}
// </vc-code>


}

fn main() {}