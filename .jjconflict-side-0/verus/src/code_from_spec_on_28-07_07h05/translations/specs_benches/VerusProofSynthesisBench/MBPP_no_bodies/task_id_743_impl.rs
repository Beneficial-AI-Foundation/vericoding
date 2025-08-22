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
    
    /* code modified by LLM (iteration 2): added bounds check to handle case when split_point == len */
    // Add elements from split_point to end
    let mut i = split_point;
    while i < len
        invariant
            split_point <= i <= len,
            new_list.len() == i - split_point,
            i <= list.len(),
            split_point <= list.len(),
            /* code modified by LLM (iteration 2): fixed syntax error by using proper if expression with curly braces */
            new_list@ == if split_point < list.len() { list@.subrange(split_point as int, i as int) } else { Seq::<u32>::empty() },
        decreases len - i,
    {
        /* code modified by LLM (iteration 2): added explicit bounds check */
        assert(i < len);
        assert(i < list.len());
        new_list.push(list[i]);
        i += 1;
    }
    
    // Add elements from 0 to split_point
    let mut j = 0;
    while j < split_point
        invariant
            0 <= j <= split_point,
            split_point <= len,
            new_list.len() == (len - split_point) + j,
            /* code modified by LLM (iteration 2): fixed syntax error by using proper if expressions with curly braces */
            new_list@ == (if split_point < list.len() { list@.subrange(split_point as int, list.len() as int) } else { Seq::<u32>::empty() }).add(
                if j > 0 { list@.subrange(0, j as int) } else { Seq::<u32>::empty() }
            ),
        decreases split_point - j,
    {
        /* code modified by LLM (iteration 2): added explicit bounds check */
        assert(j < split_point);
        assert(j < list.len());
        new_list.push(list[j]);
        j += 1;
    }
    
    new_list
}

} // verus!

fn main() {}