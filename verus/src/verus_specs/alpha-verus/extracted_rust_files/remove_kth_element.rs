use vstd::prelude::*;
verus! {

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 < k < list@.len(),
    ensures
        new_list@ == list@.subrange(0, k - 1 as int).add(
            list@.subrange(k as int, list.len() as int),
        ),
{
    let mut new_list = Vec::new();
    let mut index = 0;
    while index < (k - 1)
        invariant
            0 <= index <= k - 1,
            0 < k < list@.len(),
            new_list@ =~= list@.subrange(0, index as int),
    {
        new_list.push(list[index]);
        index += 1;
    }
    let mut index = k;
    while index < list.len()
        invariant
            k <= index <= list.len(),
            new_list@ =~= list@.subrange(0 as int, k - 1 as int).add(
                list@.subrange(k as int, index as int),
            ),
    {
        new_list.push(list[index]);
        index += 1;
    }
    assert(new_list@ == list@.subrange(0, k - 1 as int).add(
        list@.subrange(k as int, list.len() as int),
    ));
    new_list
}

fn main() {}

} // verus!
