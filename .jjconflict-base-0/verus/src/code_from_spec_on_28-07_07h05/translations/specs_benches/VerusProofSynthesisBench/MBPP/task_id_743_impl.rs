use vstd::prelude::*;

verus! {

spec fn rotation_split(len: usize, n: usize) -> (result: int) {
    len - (n % len)
}
// pure-end

fn rotate_right(list: &Vec<u32>, n: usize) -> (new_list: Vec<u32>)
    // pre-conditions-start
    requires
        list.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        new_list.len() == list.len(),
        new_list@ == list@.subrange(rotation_split(list.len(), n) as int, list@.len() as int).add(
            list@.subrange(0, rotation_split(list.len(), n) as int),
        ),
    // post-conditions-end
{
    let len = list.len();
    let split_point = len - (n % len);
    
    let mut new_list = Vec::new();
    
    // Add the suffix (from split_point to end)
    let mut i = split_point;
    while i < len
        invariant
            i <= len,
            split_point <= len,
            new_list.len() == i - split_point,
            /* code modified by LLM (iteration 3): added trigger annotation for quantifier */
            forall|j: int| 0 <= j < new_list.len() ==> #[trigger] new_list[j], 0 <= split_point + j < list.len(),
            forall|j: int| 0 <= j < new_list.len() ==> #[trigger] new_list[j] == list[split_point + j],
        decreases len - i
    {
        /* code modified by LLM (iteration 1): added bounds assertion before indexing */
        assert(split_point <= i < len);
        assert(0 <= i < list.len());
        new_list.push(list[i]);
        i = i + 1;
    }
    
    // Add the prefix (from 0 to split_point)
    let mut j = 0;
    while j < split_point
        invariant
            j <= split_point,
            split_point <= len,
            new_list.len() == (len - split_point) + j,
            /* code modified by LLM (iteration 3): added trigger annotations for all quantifiers */
            forall|k: int| 0 <= k < len - split_point ==> #[trigger] new_list[k], 0 <= split_point + k < list.len(),
            forall|k: int| 0 <= k < len - split_point ==> #[trigger] new_list[k] == list[split_point + k],
            forall|k: int| 0 <= k < j ==> #[trigger] new_list[len - split_point + k], 0 <= len - split_point + k < new_list.len(),
            forall|k: int| 0 <= k < j ==> #[trigger] list[k], 0 <= k < list.len(),
            forall|k: int| 0 <= k < j ==> #[trigger] new_list[len - split_point + k] == list[k],
        decreases split_point - j
    {
        /* code modified by LLM (iteration 1): added bounds assertions before indexing */
        assert(0 <= j < split_point);
        assert(0 <= j < list.len());
        assert(new_list.len() == (len - split_point) + j);
        new_list.push(list[j]);
        /* code modified by LLM (iteration 2): fixed type mismatch by casting j to int */
        assert(new_list[len - split_point + j] == list[j as int]);
        j = j + 1;
    }
    
    new_list
}

} // verus!

fn main() {}