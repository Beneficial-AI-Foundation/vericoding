use vstd::prelude::*;
fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

spec fn rotation_split(len: usize, n: usize) -> int {
    len - (n % len)
}

fn rotate_right(list: &Vec<u32>, n: usize) -> (new_list: Vec<u32>)
    requires
        list.len() > 0,
    ensures
        new_list.len() == list.len(),
        new_list@ == list@.subrange(rotation_split(list.len(), n) as int, list@.len() as int).add(
            list@.subrange(0, rotation_split(list.len(), n) as int),
        ),
{
    let len = list.len();
    let split_point = len - (n % len);
    
    let mut new_list = Vec::new();
    
    /* code modified by LLM (iteration 1): added comprehensive bounds establishment */
    assert(len > 0);
    assert(n % len < len);
    assert(split_point == len - (n % len));
    assert(0 <= split_point <= len);
    assert(split_point as int <= list@.len());
    
    // Add elements from split_point to end
    let mut i = split_point;
    /* code modified by LLM (iteration 1): fixed loop invariants with proper subrange bounds */
    while i < len
        invariant
            len > 0,
            0 <= split_point <= len,
            split_point <= i <= len,
            new_list.len() == i - split_point,
            i <= list.len(),
            split_point as int <= list@.len(),
            i as int <= list@.len(),
            new_list@ == list@.subrange(split_point as int, i as int),
        decreases len - i,
    {
        /* code modified by LLM (iteration 1): added comprehensive bounds assertions */
        assert(split_point <= i < len);
        assert(i < len);
        assert(len == list.len());
        assert(i < list.len());
        new_list.push(list[i]);
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 1): added assertion to establish subrange bounds for second loop */
    assert(split_point as int <= len as int);
    assert(len as int == list@.len());
    assert(split_point as int <= list@.len());
    
    // Add elements from beginning to split_point
    let mut j = 0;
    /* code modified by LLM (iteration 1): fixed loop invariants with proper bounds and subrange constraints */
    while j < split_point
        invariant
            len > 0,
            0 <= split_point <= len,
            0 <= j <= split_point,
            new_list.len() == (len - split_point) + j,
            j <= list.len(),
            split_point <= list.len(),
            len == list.len(),
            split_point as int <= list@.len(),
            j as int <= split_point as int,
            j as int <= list@.len(),
            len as int == list@.len(),
            new_list@ == list@.subrange(split_point as int, len as int).add(
                list@.subrange(0, j as int)
            ),
        decreases split_point - j,
    {
        /* code modified by LLM (iteration 1): added comprehensive bounds checking before array access */
        assert(0 <= j < split_point);
        assert(split_point <= len);
        assert(len == list.len());
        assert(j < split_point);
        assert(split_point <= list.len());
        assert(j < list.len());
        new_list.push(list[j]);
        j = j + 1;
    }
    
    new_list
}

} // verus!