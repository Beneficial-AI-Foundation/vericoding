// <vc-preamble>
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected type casting errors for `nat` and `int` to `usize` for array indexing where necessary. */
fn count_frequencies(nums: &Vec<i32>) -> (freq_map: Map<i32, nat>)
    ensures
        forall|x: i32| freq_map.dom().contains(x) <==> nums@.contains(x),
        forall|x: i32| freq_map.dom().contains(x) ==> freq_map[x] == nums@.filter(|e: i32| e == x).len(),
{
    let mut freq_map = Map::<i32, nat>::empty();
    let mut i: nat = 0;
    while (i as usize) < nums.len()
        invariant
            0 <= i as usize <= nums.len(),
            forall|x: i32| freq_map.dom().contains(x) <==> nums@.subsequence(0, i as int).contains(x),
            forall|x: i32| freq_map.dom().contains(x) ==> freq_map[x] == nums@.subsequence(0, i as int).filter(|e: i32| e == x).len(),
        decreases nums.len() - (i as usize)
    {
        let num = nums[i as usize];
        let count = if freq_map.dom().contains(num) {
            freq_map[num] + 1
        } else {
            1
        };
        freq_map = freq_map.insert(num, count);
        i = i + 1;
    }
    freq_map
}

pub struct ElementData {
    pub value: i32,
    pub frequency: nat,
}

impl ElementData {
    pub open spec fn view(&self) -> (i32, nat) {
        (self.value, self.frequency)
    }
}

fn find_max_element_in_seq(data_seq: &Seq<ElementData>) -> (max_idx: nat)
    requires
        data_seq.len() > 0,
    ensures
        0 <= max_idx < data_seq.len(),
        forall|i: nat| 0 <= i < data_seq.len() ==> data_seq.index(i as int).frequency <= data_seq.index(max_idx as int).frequency,
{
    let mut max_idx: nat = 0;
    let mut i: nat = 1;
    while i < data_seq.len()
        invariant
            0 < data_seq.len(),
            0 <= max_idx < i,
            i <= data_seq.len(),
            forall|j: nat| 0 <= j < i ==> data_seq.index(j as int).frequency <= data_seq.index(max_idx as int).frequency,
        decreases data_seq.len() - i
    {
        if data_seq.index(i as int).frequency > data_seq.index(max_idx as int).frequency {
            max_idx = i;
        }
        i = i + 1;
    }
    max_idx
}
// </vc-helpers>

// <vc-spec>
fn top_k_frequent(nums: &Vec<i32>, k: usize) -> (result: Vec<i32>)
    requires 
        k <= nums@.to_set().len(),
    ensures
        result.len() == k,
        forall|x: i32| result@.contains(x) ==> nums@.contains(x),
        result@.no_duplicates(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type casting errors for `nat` and `int` to `usize` for array indexing where necessary. */
{
    let freq_map = count_frequencies(nums);

    let mut freq_vec_s: Seq<ElementData> = Seq::empty();
    for num in freq_map.dom().to_seq().into_iter() {
        freq_vec_s = freq_vec_s.push(ElementData { value: num, frequency: freq_map[num] });
    }

    let mut result_vec: Vec<i32> = Vec::new();
    let mut current_freq_vec_s = freq_vec_s;

    while result_vec.len() < k
        invariant
            result_vec.len() <= k,
            result_vec.len() as nat <= current_freq_vec_s.len(),
            current_freq_vec_s.len() + result_vec.len() as nat == freq_map.len(),
            forall|x: i32| (result_vec@).contains(x) ==> freq_map.dom().contains(x),
            result_vec@.no_duplicates(),
            forall|x: i32| (result_vec@).contains(x) ==> 
                forall|ed: ElementData| current_freq_vec_s.contains(ed) ==> 
                    freq_map.dom().contains(x) && freq_map.dom().contains(ed.value) && freq_map[x] >= freq_map[ed.value],
        decreases k - result_vec.len()
    {
        if current_freq_vec_s.len() == (0 as nat) {
            // Should not happen given k <= nums@.to_set().len()
            return result_vec;
        }

        let max_idx = find_max_element_in_seq(&current_freq_vec_s);
        let top_element = current_freq_vec_s.index(max_idx as int);

        result_vec.push(top_element.value);

        // Remove the top_element from current_freq_vec_s
        let mut new_freq_vec_s = Seq::empty();
        let mut i: nat = 0;
        while i < current_freq_vec_s.len()
            invariant
                0 <= i <= current_freq_vec_s.len(),
                new_freq_vec_s.len() == i || current_freq_vec_s.index(max_idx as int).value == top_element.value && new_freq_vec_s.len() == (i as int - 1) as nat,
                forall|j: nat| 0 <= j < new_freq_vec_s.len() ==> new_freq_vec_s.index(j as int).value != top_element.value,
                forall|j: nat| 0 <= j < i && j != max_idx ==> new_freq_vec_s.contains(current_freq_vec_s.index(j as int)),
                current_freq_vec_s.len() > 0,
            decreases current_freq_vec_s.len() - i
        {
            if i != max_idx {
                new_freq_vec_s = new_freq_vec_s.push(current_freq_vec_s.index(i as int));
            }
            i = i + 1;
        }
        current_freq_vec_s = new_freq_vec_s;
    }

    result_vec
}
// </vc-code>

}
fn main() {}