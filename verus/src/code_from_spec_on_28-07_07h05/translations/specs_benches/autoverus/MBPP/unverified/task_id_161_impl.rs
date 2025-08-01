use vstd::prelude::*;

fn main() {}

verus! {

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    for i in 0..str.len()
        invariant
            forall|j: int| 0 <= j < i ==> str[j] != key,
    {
        if str[i] == key {
            return true;
        }
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
    
    for i in 0..arr1.len()
        invariant
            forall|j: int| 0 <= j < result.len() ==> (arr1@.contains(#[trigger] result[j]) && !arr2@.contains(#[trigger] result[j])),
            forall|j: int| 0 <= j < i ==> (arr2@.contains(#[trigger] arr1[j]) || result@.contains(#[trigger] arr1[j])),
    {
        if !contains(arr2, arr1[i as int]) {
            result.push(arr1[i as int]);
            /* code modified by LLM (iteration 4): Added assertion with proper type casting */
            assert(result@.contains(arr1[i as int]));
        } else {
            /* code modified by LLM (iteration 4): Added assertion with proper type casting */
            assert(arr2@.contains(arr1[i as int]));
        }
        /* code modified by LLM (iteration 4): Split assertion with proper type casting */
        assert(arr2@.contains(arr1[i as int]) || result@.contains(arr1[i as int]));
        assert(forall|j: int| 0 <= j < i + 1 ==> (arr2@.contains(#[trigger] arr1[j]) || result@.contains(#[trigger] arr1[j])));
    }
    
    result
}

} // verus!