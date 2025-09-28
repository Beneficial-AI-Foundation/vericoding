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
/* helper modified by LLM (iteration 5): convert Vec<i8> to Seq<int> */
spec fn vec_to_seq(v: Vec<i8>) -> Seq<int> {
    v@.map(|i, x| x as int)
}

/* helper modified by LLM (iteration 5): count good subarrays starting at 'start' with end < upto */
spec fn count_from_start(digits: Seq<int>, start: int, upto: int) -> int
    requires
        0 <= start <= upto <= digits.len(),
    decreases upto - start
{
    if start >= upto { 0 } else { count_from_start(digits, start, upto - 1) + (if is_good_subarray(digits, start, upto - 1) { 1 } else { 0 }) }
}

/* helper modified by LLM (iteration 5): count total good subarrays for starts in [0, upto) with ends < n */
spec fn count_prefix(digits: Seq<int>, upto: int, n: int) -> int
    requires
        0 <= upto <= n <= digits.len(),
    decreases upto
{
    if upto == 0 { 0 } else { count_prefix(digits, upto - 1, n) + count_from_start(digits, upto - 1, n) }
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
    /* code modified by LLM (iteration 5): use ghost/tracked vars and double loop counting */
    let tracked n: nat = digits.len();
    let ghost seq: Seq<int> = digits@.map(|i, x| x as int);
    let tracked mut count_int: int = 0;
    let tracked mut i: nat = 0;
    while i < n
        invariant
            0 <= i <= n,
            count_int == count_prefix(seq, i as int, n as int),
        decreases n - i
    {
        let tracked mut curr_sum: int = 0;
        let tracked mut j: nat = i;
        while j < n
            invariant
                i <= j <= n,
                curr_sum == sum(seq.subrange(i as int, j as int)),
                count_int == count_prefix(seq, i as int, n as int) + count_from_start(seq, i as int, j as int),
            decreases n - j
        {
            curr_sum = curr_sum + seq@[j as int];
            if curr_sum == (j as int - i as int + 1) {
                count_int = count_int + 1;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    count_int as i8
}
// </vc-code>


}

fn main() {}