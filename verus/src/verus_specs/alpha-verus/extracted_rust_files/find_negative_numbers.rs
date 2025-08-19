use vstd::prelude::*;

verus! {

fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
{
    let mut negative_list: Vec<i32> = Vec::new();
    let input_len = arr.len();

    assert(arr@.take(0int).filter(|x: i32| x < 0) == Seq::<i32>::empty());
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            negative_list@ == arr@.take(index as int).filter(|x: i32| x < 0),
    {
        if (arr[index] < 0) {
            negative_list.push(arr[index]);
        }
        assert(arr@.take((index + 1) as int).drop_last() == arr@.take(index as int));
        reveal(Seq::filter);
        index += 1;
    }
    assert(arr@ == arr@.take(input_len as int));
    negative_list
}

fn main() {}

} // verus!
