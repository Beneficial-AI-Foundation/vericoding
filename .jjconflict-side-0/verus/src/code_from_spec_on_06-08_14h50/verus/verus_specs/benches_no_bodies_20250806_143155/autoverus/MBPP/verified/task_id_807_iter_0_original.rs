use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    ensures
        if let Some(idx) = index {
    return None;  // TODO: Remove this line and implement the function body
        } else {
            forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)
        },
{
    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            arr@.take(index as int) =~= arr@.take(index as int).filter(|x: u32| x % 2 == 0),
    {
        if (arr[index] % 2 != 0) {
            return Some(index);
        }
        assert(arr@.take((index + 1) as int).drop_last() == arr@.take(index as int));
        reveal(Seq::filter);
        index += 1;
    }
    assert(arr@ == arr@.take(input_len as int));
    None
}

} // verus!
