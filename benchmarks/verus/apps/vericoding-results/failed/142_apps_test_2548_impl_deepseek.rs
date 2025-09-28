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

/* helper modified by LLM (iteration 5): Fixed type conversions and forall method */
proof fn ghost_digit(digit: i8) -> (result: int)
    ensures result == digit as int
{
    digit as int
}

/* helper modified by LLM (iteration 5): Updated lemma with correct method name */
proof fn lemma_freq_map_update_correct(freq_map: Map<int, int>, key: int) -> (new_map: Map<int, int>)
    ensures
        new_map == freq_map.insert(key, if freq_map.dom().contains(key) { freq_map[key] + 1 } else { 1 }),
        new_map.dom().all(|k| new_map[k] >= 0),
        freq_map.dom().contains(0) && freq_map[0] >= 1 ==> new_map.dom().contains(0) && new_map[0] >= 1
{
    freq_map.insert(key, if freq_map.dom().contains(key) { freq_map[key] + 1 } else { 1 })
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
    /* code modified by LLM (iteration 5): Fixed type errors and method calls */
    let vec_len: usize = digits.len();
    let mut count: i8 = 0;
    let mut freq_map: Map<int, int> = map![0 => 1];
    let mut current_sum: int = 0;
    let mut current_count: int = 0;
    
    let mut pos: usize = 0;
    while pos < vec_len
        invariant 
            pos <= vec_len,
            current_sum >= 0,
            current_count == pos as int,
            count as int == count_good_subarrays(digits@.map(|i, x| x as int).subrange(0, pos as int)),
            freq_map.dom().all(|k| freq_map[k] >= 0),
            freq_map.dom().contains(0) && freq_map[0] >= 1
    {
        let digit_value: int = ghost_digit(digits[pos]);
        current_sum = current_sum + digit_value;
        current_count = current_count + 1;
        let diff: int = current_count - current_sum;
        
        if freq_map.dom().contains(diff) {
            let freq_val: int = freq_map[diff];
            count = count + (freq_val as i8);
        }
        
        freq_map = lemma_freq_map_update_correct(freq_map, diff);
        
        pos = pos + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}