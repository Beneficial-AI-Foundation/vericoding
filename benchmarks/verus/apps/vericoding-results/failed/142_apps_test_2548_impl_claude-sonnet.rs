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
/* helper modified by LLM (iteration 5): fixed type annotation in fold_left closure */
fn lemma_sum_drop_first(s: Seq<int>)
    requires s.len() > 0
    ensures sum(s) == s[0] + sum(s.drop_first())
{
}

fn lemma_sum_subrange_property(s: Seq<int>, start: int, end: int)
    requires 0 <= start <= end < s.len()
    ensures sum(s.subrange(start, end + 1)) == s.subrange(start, end + 1).fold_left(0, |acc: int, x: int| acc + x)
{
}

fn lemma_good_subarray_characterization(digits: Seq<int>, start: int, end: int)
    requires 
        0 <= start <= end < digits.len(),
        valid_input(digits)
    ensures 
        is_good_subarray(digits, start, end) <==> 
        (sum(digits.subrange(0, end + 1)) - (end + 1)) == (sum(digits.subrange(0, start)) - start)
{
}

fn lemma_freq_map_property(digits: Seq<int>, pos: int, sum_val: int)
    requires 
        0 <= pos <= digits.len(),
        valid_input(digits)
    ensures 
        pos - sum_val >= -(digits.len() as int) && pos - sum_val <= digits.len() as int
{
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
    /* code modified by LLM (iteration 5): added decreases clause to fix verification error */
    let mut freq_map: std::collections::HashMap<i32, i32> = std::collections::HashMap::new();
    freq_map.insert(0, 1);
    
    let mut current_sum: i32 = 0;
    let mut result: i32 = 0;
    let mut pos: usize = 0;
    
    while pos < digits.len()
        invariant
            0 <= pos <= digits.len(),
            current_sum >= 0,
            result >= 0,
            freq_map.len() >= 1
        decreases digits.len() - pos
    {
        current_sum += digits[pos] as i32;
        let current_count = (pos + 1) as i32;
        let diff = current_count - current_sum;
        
        if let Some(freq) = freq_map.get(&diff) {
            result += *freq;
        }
        
        let new_freq = if let Some(freq) = freq_map.get(&diff) {
            *freq + 1
        } else {
            1
        };
        freq_map.insert(diff, new_freq);
        
        pos += 1;
    }
    
    result as i8
}
// </vc-code>


}

fn main() {}