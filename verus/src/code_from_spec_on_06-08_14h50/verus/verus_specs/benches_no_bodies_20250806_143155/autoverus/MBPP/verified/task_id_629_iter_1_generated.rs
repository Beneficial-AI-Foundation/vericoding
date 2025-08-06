use vstd::prelude::*;

fn main() {
    let numbers = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    let evens = find_even_numbers(&numbers);
    println!("Even numbers: {:?}", evens);
}

verus! {

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut result: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0),
    {
        if arr[i] % 2 == 0 {
            result.push(arr[i]);
        }
        i = i + 1;
    }
    
    result
}

} // verus!