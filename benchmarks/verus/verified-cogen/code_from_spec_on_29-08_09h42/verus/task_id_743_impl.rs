use vstd::prelude::*;

verus! {

spec fn rotation_split(len: usize, n: usize) -> (result: int) {
    len - (n % len)
}
// pure-end

// <vc-helpers>
proof fn lemma_rotation_split_bounds(len: usize, n: usize)
    requires len > 0
    ensures 0 <= rotation_split(len, n) <= len
{
    let split = rotation_split(len, n);
    assert(split == len - (n % len));
    assert(0 <= n % len < len);
    assert(0 <= len - (n % len) <= len);
}

proof fn lemma_subrange_add_length<T>(s: Seq<T>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= s.len()
    ensures s.subrange(j, k).add(s.subrange(i, j)).len() == k - i
{
}

proof fn lemma_rotation_split_in_bounds(len: usize, n: usize)
    requires len > 0
    ensures rotation_split(len, n) >= 0 && rotation_split(len, n) <= len
{
    lemma_rotation_split_bounds(len, n);
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
    
    proof {
        lemma_rotation_split_bounds(len, n);
    }
    
    /* code modified by LLM (iteration 5): compute split directly as usize to avoid spec-to-exec conversion */
    let split = len - (n % len);
    
    let mut result = Vec::new();
    
    // Add elements from split position to end
    let mut i = split;
    while i < len
        invariant
            split <= i <= len,
            result.len() == i - split,
            result@ == list@.subrange(split as int, i as int),
    {
        result.push(list[i]);
        i += 1;
    }
    
    // Add elements from beginning to split position
    let mut j = 0;
    while j < split
        invariant
            0 <= j <= split,
            result.len() == (len - split) + j,
            result@ == list@.subrange(split as int, len as int).add(
                list@.subrange(0, j as int)
            ),
    {
        result.push(list[j]);
        j += 1;
    }
    
    proof {
        lemma_subrange_add_length(list@, 0, split as int, len as int);
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}