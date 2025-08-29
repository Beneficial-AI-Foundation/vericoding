use vstd::prelude::*;

verus! {

spec fn rotation_split(len: usize, n: usize) -> (result: int) {
    len - (n % len)
}
// pure-end

// <vc-helpers>
proof fn lemma_rotation_split_bounds(len: usize, n: usize)
    requires len > 0
    ensures 
        0 <= rotation_split(len, n) <= len,
        rotation_split(len, n) as int == len - (n % len) as int
{
    assert(n % len < len);
    assert(rotation_split(len, n) == len - (n % len));
}

proof fn lemma_subrange_add_length<T>(s: Seq<T>, split: int)
    requires 
        0 <= split <= s.len()
    ensures
        s.subrange(split, s.len() as int).add(s.subrange(0, split)).len() == s.len()
{
}

proof fn lemma_split_to_usize(len: usize, n: usize)
    requires len > 0
    ensures 
        rotation_split(len, n) >= 0,
        rotation_split(len, n) <= len
{
    assert(n % len < len);
    assert(rotation_split(len, n) == len - (n % len));
}

proof fn lemma_int_to_usize_conversion(x: int, bound: usize)
    requires 0 <= x <= bound
    ensures x as usize <= bound
{
}

proof fn lemma_rotation_split_is_nat(len: usize, n: usize)
    requires len > 0
    ensures rotation_split(len, n) is nat
{
    assert(n % len < len);
    assert(rotation_split(len, n) == len - (n % len));
    assert(rotation_split(len, n) >= 0);
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

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
    let split = rotation_split(len, n);
    
    proof {
        lemma_rotation_split_bounds(len, n);
        lemma_split_to_usize(len, n);
        lemma_int_to_usize_conversion(split, len);
        lemma_rotation_split_is_nat(len, n);
    }
    
    let mut new_list = Vec::new();
    
    /* code modified by LLM (iteration 5): convert int to nat first, then to usize */
    let split_nat = split as nat;
    let split_usize: usize = split_nat as usize;
    let mut i: usize = split_usize;
    while i < len
        invariant
            split <= i <= len,
            new_list.len() == i - split_usize,
            new_list@ == list@.subrange(split as int, i as int),
            len > 0,
            split == rotation_split(len, n),
            0 <= split <= len,
            split_usize == split_nat as usize,
    {
        new_list.push(list[i]);
        i += 1;
    }
    
    /* code modified by LLM (iteration 5): use split_usize for bounds checking */
    let mut j: usize = 0;
    while j < split_usize
        invariant
            0 <= j <= split,
            new_list.len() == (len - split_usize) + j,
            new_list@ == list@.subrange(split as int, len as int).add(list@.subrange(0, j as int)),
            len > 0,
            split == rotation_split(len, n),
            0 <= split <= len,
            split_usize == split_nat as usize,
    {
        new_list.push(list[j]);
        j += 1;
    }
    
    proof {
        lemma_subrange_add_length(list@, split as int);
        assert(new_list@ == list@.subrange(split as int, len as int).add(list@.subrange(0, split as int)));
    }
    
    new_list
}
// </vc-code>

} // verus!

fn main() {}