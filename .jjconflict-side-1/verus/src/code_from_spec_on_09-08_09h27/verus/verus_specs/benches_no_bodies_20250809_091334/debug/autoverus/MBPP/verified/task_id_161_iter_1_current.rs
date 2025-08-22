use vstd::prelude::*;

fn main() {
    // Simple main function - can be empty or contain test code
    let v1 = vec![1, 2, 3, 4, 5];
    let v2 = vec![2, 4];
    let result = remove_elements(&v1, &v2);
    println!("Result: {:?}", result);
}

verus! {

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
    // The proof follows from the definition of push operation
    // All existing elements remain at the same indices
    // The new element is placed at the end (index l)
}

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut idx = 0;
    while idx < str.len()
        invariant
            0 <= idx <= str.len(),
            forall|k: int| 0 <= k < idx ==> str[k] != key,
    {
        if str[idx] == key {
            return true;
        }
        idx += 1;
    }
    false
}

fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
                #[trigger] arr1[i],
            )),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|k: int|
                0 <= k < result.len() ==> (arr1@.contains(#[trigger] result[k]) && !arr2@.contains(
                    #[trigger] result[k],
                )),
            forall|k: int|
                0 <= k < i ==> (arr2@.contains(#[trigger] arr1[k]) || result@.contains(
                    #[trigger] arr1[k],
                )),
    {
        if !contains(arr2, arr1[i]) {
            result.push(arr1[i]);
        }
        i += 1;
    }
    
    result
}

} // verus!