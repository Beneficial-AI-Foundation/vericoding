use vstd::prelude::*;

fn main() {
    let arr = vec![1, 2, 3];
    let result = insert_before_each(&arr, 0);
    println!("Result: {:?}", result);
}

verus! {

fn insert_before_each(arr: &Vec<i32>, elem: i32) -> (result: Vec<i32>)
    ensures
        result@.len() == (2 * arr.len()),
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k] == elem,
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k + 1] == arr[k],
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@.len() == 2 * i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[2 * k] == elem,
            forall|k: int| 0 <= k < i ==> #[trigger] result[2 * k + 1] == arr[k],
    {
        result.push(elem);
        result.push(arr[i]);
        i += 1;
    }
    
    result
}

} // verus!