use vstd::prelude::*;
fn main() {}

verus! {

spec fn rotation_split(len: usize, n: usize) -> int {
    len - (n % len)
}

//IMPL rotate_right
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
    
    /* code modified by LLM (iteration 3): added assertion to establish split_point bounds */
    assert(split_point <= len);
    assert(split_point == len - (n % len));
    assert(n % len < len);
    assert(split_point >= 0);
    
    let mut new_list = Vec::new();
    
    // Add elements from split_point to end
    let mut i = split_point;
    /* code modified by LLM (iteration 3): improved invariants with len consistency */
    while i < len
        invariant
            list.len() > 0,
            len == list.len(),
            split_point <= len,
            split_point <= i <= len,
            new_list.len() == i - split_point,
            split_point as int <= i as int <= len as int,
            split_point as int <= list@.len(),
            i as int <= list@.len(),
            new_list@ == list@.subrange(split_point as int, i as int),
        decreases len - i,
    {
        /* code modified by LLM (iteration 3): removed redundant assertion that was failing */
        assert(i < len);
        assert(i < list.len());
        new_list.push(list[i]);
        i += 1;
    }
    
    // Add elements from beginning to split_point
    let mut j = 0;
    /* code modified by LLM (iteration 3): improved invariants with len consistency */
    while j < split_point
        invariant
            list.len() > 0,
            len == list.len(),
            split_point <= len,
            0 <= j <= split_point,
            new_list.len() == (len - split_point) + j,
            split_point as int <= len as int,
            j as int <= split_point as int,
            j as int <= len as int,
            0 <= j as int,
            split_point as int <= list@.len(),
            len as int == list@.len(),
            new_list@ == list@.subrange(split_point as int, len as int).add(
                list@.subrange(0, j as int)
            ),
        decreases split_point - j,
    {
        /* code modified by LLM (iteration 3): removed failing assertion and kept necessary ones */
        assert(j < split_point);
        assert(split_point <= len);
        assert(j < list.len());
        new_list.push(list[j]);
        j += 1;
    }
    
    new_list
}

} // verus!