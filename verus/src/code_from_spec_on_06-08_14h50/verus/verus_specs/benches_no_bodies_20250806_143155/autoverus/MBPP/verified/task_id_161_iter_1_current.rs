use vstd::prelude::*;

fn main() {
    let arr1 = vec![1, 2, 3, 4, 5];
    let arr2 = vec![2, 4];
    let result = remove_elements(&arr1, &arr2);
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
    // The proof is automatic in Verus for these sequence properties
}

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut idx = 0;
    while idx < str.len()
        invariant
            forall|i: int| 0 <= i < idx ==> str[i] != key,
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
    let mut idx = 0;
    
    while idx < arr1.len()
        invariant
            0 <= idx <= arr1.len(),
            forall|i: int|
                0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(
                    #[trigger] result[i],
                )),
            forall|i: int|
                0 <= i < idx ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
                    #[trigger] arr1[i],
                )),
    {
        let current_element = arr1[idx];
        if !contains(arr2, current_element) {
            result.push(current_element);
        }
        idx += 1;
    }
    
    result
}

} // verus!