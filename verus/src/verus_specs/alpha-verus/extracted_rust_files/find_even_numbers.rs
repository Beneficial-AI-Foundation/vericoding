use vstd::prelude::*;

verus! {

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let input_len = arr.len();

    assert(arr@.take(0int).filter(|x: u32| x % 2 == 0) == Seq::<u32>::empty());
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            even_numbers@ == arr@.take(index as int).filter(|x: u32| x % 2 == 0),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }
        assert(arr@.take((index + 1) as int).drop_last() == arr@.take(index as int));
        reveal(Seq::filter);
        index += 1;
    }
    assert(arr@ == arr@.take(input_len as int));
    even_numbers
}

fn main() {}

} // verus!
