use vstd::prelude::*;

fn main() {}

verus! {

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut idx = 0;
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while idx < str.len()
        invariant
            forall|i: int| 0 <= i < idx ==> str[i] != key,
        decreases str.len() - idx
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
    
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|j: int|
                0 <= j < result.len() ==> (arr1@.contains(#[trigger] result[j]) && !arr2@.contains(
                    #[trigger] result[j],
                )),
            forall|j: int|
                0 <= j < i ==> (arr2@.contains(#[trigger] arr1[j]) || result@.contains(
                    #[trigger] arr1[j],
                )),
        decreases arr1.len() - i
    {
        let element = arr1[i];
        if !contains(arr2, element) {
            result.push(element);
        }
        i += 1;
    }
    
    result
}

} // verus!