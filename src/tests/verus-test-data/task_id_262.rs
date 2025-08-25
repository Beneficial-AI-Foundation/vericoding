use vstd::prelude::*;


verus! {

fn split_array(list: &Vec<i32>, l: usize) -> (new_list: (Vec<i32>, Vec<i32>))
    // pre-conditions-start
    requires
        list@.len() > 0,
        0 < l < list@.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        new_list.0@ == list@.subrange(0, l as int),
        new_list.1@ == list@.subrange(l as int, list.len() as int),
    // post-conditions-end
{
    // impl-start
    let mut part1: Vec<i32> = Vec::new();
    let mut index = 0;
    while index < l
        // invariants-start
        invariant
            0 < l < list@.len(),
            0 <= index <= l,
            part1@ =~= list@.subrange(0, index as int),
        // invariants-end
    {
        part1.push(list[index]);
        index += 1;
    }
    let mut part2: Vec<i32> = Vec::new();
    index = l;
    while index < list.len()
        // invariants-start
        invariant
            l <= index <= list.len(),
            part2@ =~= list@.subrange(l as int, index as int),
        // invariants-end
    {
        part2.push(list[index]);
        index += 1;
    }

    (part1, part2)
    // impl-end
}

} // verus!

fn main() {}
