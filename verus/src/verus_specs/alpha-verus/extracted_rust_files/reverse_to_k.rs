use vstd::prelude::*;
verus! {

fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        reversed_list@ == list@.subrange(0, n as int).reverse().add(
            list@.subrange(n as int, list.len() as int),
        ),
{
    let mut reversed_list = Vec::new();
    let mut index = 0;
    while index < n
        invariant
            0 < n < list@.len(),
            0 <= index <= n,
            reversed_list.len() == index,
            forall|k: int| 0 <= k < index ==> reversed_list[k] == list[n - 1 - k],
    {
        reversed_list.push(list[n - 1 - index]);
        index += 1;
    }
    index = n;
    while index < list.len()
        invariant
            n <= index <= list.len(),
            reversed_list@ =~= list@.subrange(0, n as int).reverse().add(
                list@.subrange(n as int, index as int),
            ),
    {
        reversed_list.push(list[index]);
        index += 1;
    }
    reversed_list
}

fn main() {}

} // verus!
