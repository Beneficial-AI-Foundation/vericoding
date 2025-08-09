use vstd::prelude::*;

fn main() {
    let arr = vec![1, -2, 3, -4, 5, -6];
    let negatives = find_negative_numbers(&arr);
    println!("Negative numbers: {:?}", negatives);
}

verus! {

fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: i32| x < 0),
    {
        if arr[i] < 0 {
            result.push(arr[i]);
        }
        i += 1;
    }
    
    result
}

} // verus!