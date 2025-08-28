use vstd::prelude::*;

verus! {

spec fn rotation_split(len: usize, n: usize) -> (result: int) {
    len - (n % len)
}
// pure-end

// <vc-helpers>
spec fn rotation_split_in_bounds(len: usize, n: usize) -> bool {
    len > 0 ==> 0 <= rotation_split(len, n) <= len
}

proof fn rotation_split_bounds(len: usize, n: usize)
    requires len > 0
    ensures 0 <= rotation_split(len, n) <= len
{
    let split = rotation_split(len, n);
    let mod_val = n % len;
    assert(0 <= mod_val < len);
    assert(split == len - mod_val);
    assert(0 <= split <= len);
}

proof fn subrange_properties(list: &Vec<u32>, split: int)
    requires 
        list.len() > 0,
        0 <= split <= list.len()
    ensures
        list@.subrange(split, list@.len() as int).add(list@.subrange(0, split)).len() == list@.len()
{
    assert(list@.subrange(split, list@.len() as int).len() == list@.len() - split);
    assert(list@.subrange(0, split).len() == split);
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let len = list.len();
    let split_int = rotation_split(len, n);
    
    proof {
        rotation_split_bounds(len, n);
        subrange_properties(list, split_int);
    }
    
    let split = split_int as usize;
    
    let mut result = Vec::new();
    
    // Add elements from split position to end
    let mut i: usize = split;
    while i < len
        invariant
            split <= i <= len,
            result.len() == i - split,
            forall |j: int| 0 <= j < (i as int) - (split as int) ==> result@[j] == list@[j + (split as int)]
    {
        result.push(list[i]);
        i = i + 1;
    }
    
    // Add elements from beginning to split position
    let mut j: usize = 0;
    while j < split
        invariant
            0 <= j <= split,
            result.len() == (len - split) + j,
            forall |k: int| 0 <= k < (len as int) - (split as int) ==> result@[k] == list@[k + (split as int)],
            forall |k: int| (len as int) - (split as int) <= k < result.len() ==> result@[k] == list@[k - ((len as int) - (split as int))]
    {
        result.push(list[j]);
        j = j + 1;
    }
    
    proof {
        assert(result.len() == (len - split) + split);
        assert(result.len() == len);
        
        let right_part = list@.subrange(split_int, len as int);
        let left_part = list@.subrange(0, split_int);
        let expected = right_part.add(left_part);
        
        assert(result@ =~= expected);
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}