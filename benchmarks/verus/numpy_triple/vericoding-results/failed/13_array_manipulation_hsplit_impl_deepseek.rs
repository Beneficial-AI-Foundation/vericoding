// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn index_in_partition_valid(arr_len: nat, k: nat, part_idx: int, elem_idx: int)
    requires
        k > 0,
        arr_len % k == 0,
        0 <= part_idx < k as int,
        0 <= elem_idx < (arr_len / k) as int
    ensures
        let part_size = (arr_len / k) as int;
        part_idx * part_size + elem_idx >= 0
{
    let part_size = (arr_len / k) as int;
    assert(part_idx >= 0 && elem_idx >= 0);
    assert(part_size > 0);
    assert(part_idx * part_size + elem_idx >= 0);
}

proof fn element_bounds_valid(arr_len: nat, k: nat, i: int)
    requires
        k > 0,
        arr_len % k == 0,
        0 <= i < arr_len as int
    ensures
        (i / ((arr_len / k) as int)) as int >= 0,
        (i / ((arr_len / k) as int)) as int < k as int,
        (i % ((arr_len / k) as int)) as int >= 0,
        (i % ((arr_len / k) as int)) as int < (arr_len / k) as int
{
    let part_size = (arr_len / k) as int;
    assert(i >= 0 && i < arr_len as int);
    assert(part_size > 0);
    assert(i / part_size >= 0);
    assert(i / part_size < k as int);
    assert(i % part_size >= 0);
    assert(i % part_size < part_size);
}

fn partition_length(arr_len: nat, k: nat) -> (len_per_part: nat)
    requires
        k > 0,
        arr_len % k == 0
    ensures
        (len_per_part as int) * (k as int) == arr_len as int
{
    let part_size = arr_len / k;
    assert(part_size as int * k as int == arr_len as int) by {
        proof { }
    }
    part_size
}

// </vc-helpers>

// <vc-spec>
fn hsplit(arr: Vec<f32>, k: usize) -> (result: Vec<Vec<f32>>)
    requires 
        k > 0,
        arr@.len() % (k as nat) == 0,
    ensures
        result@.len() == k,
        forall|part_idx: int| 0 <= part_idx < k as int ==> result@[part_idx].len() == arr@.len() / (k as nat),
        forall|part_idx: int, elem_idx: int| 
            0 <= part_idx < k as int && 0 <= elem_idx < (arr@.len() / (k as nat)) as int ==>
            #[trigger] result@[part_idx][elem_idx] == arr@[part_idx * ((arr@.len() / (k as nat)) as int) + elem_idx],
        forall|i: int| 0 <= i < arr@.len() ==> 
            exists|p: int, e: int| 
                0 <= p < k as int && 0 <= e < (arr@.len() / (k as nat)) as int &&
                i == p * ((arr@.len() / (k as nat)) as int) + e &&
                #[trigger] arr@[i] == result@[p][e]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by using natural number arithmetic */
    let total_len = arr.len() as nat;
    let part_size = partition_length(total_len, k as nat) as usize;
    
    let mut result = Vec::new();
    let mut part_idx: usize = 0;
    
    while part_idx < k
        invariant
            0 <= part_idx <= k,
            result@.len() == part_idx,
            forall|p: int| 0 <= p < part_idx as int ==> result@[p].len() == part_size as int,
            forall|p: int, e: int| 
                0 <= p < part_idx as int && 0 <= e < part_size as int ==>
                #[trigger] result@[p][e] == arr@[p * (part_size as int) + e],
            forall|i: int| 0 <= i < (part_idx as int) * (part_size as int) ==> 
                exists|p: int, e: int| 
                    0 <= p < part_idx as int && 0 <= e < part_size as int &&
                    i == p * (part_size as int) + e &&
                    #[trigger] arr@[i] == result@[p][e],
            total_len as int == (k as int) * (part_size as int)
        decreases k - part_idx
    {
        let mut current_part = Vec::new();
        let mut elem_idx: usize = 0;
        
        while elem_idx < part_size
            invariant
                0 <= elem_idx <= part_size,
                current_part@.len() == elem_idx,
                forall|e: int| 0 <= e < elem_idx as int ==> 
                    #[trigger] current_part@[e] == arr@[part_idx * (part_size as int) + e],
                forall|e: int| 0 <= e < elem_idx as int ==> 
                    part_idx * (part_size as int) + e < arr@.len() as int
            decreases part_size - elem_idx
        {
            index_in_partition_valid(total_len, k as nat, part_idx as int, elem_idx as int);
            current_part.push(arr[part_idx * part_size + elem_idx]);
            elem_idx += 1;
        }
        
        result.push(current_part);
        part_idx += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}