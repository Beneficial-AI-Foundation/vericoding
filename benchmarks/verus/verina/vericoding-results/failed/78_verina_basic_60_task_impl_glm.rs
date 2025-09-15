// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
spec fn index_in_vec<T>(v: &Vec<T>, elem: T) -> Option<nat> { decreases v.len(); if v.len() == 0 { None } else { if v[0] == elem { Some(0) } else { let res = index_in_vec(&v[1..].to_vec(), elem); match res { Some(i) => Some(i + 1), None => None } } } } proof lemma index_in_vec_correct<T>(v: &Vec<T>, elem: T) ensures index_in_vec(v, elem).is_some() ==> v@[index_in_vec(v, elem).unwrap()] == elem { decreases v.len(); if v.len() == 0 { } else { if v[0] == elem { } else { let subvec = v[1..].to_vec(); if index_in_vec(&subvec, elem).is_some() { let subidx = index_in_vec(&subvec, elem).unwrap(); assert(v@[subidx + 1] == subvec@[subidx]); } } } }
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> is_even(#[trigger] result[i]),
        forall|i: int| 0 <= i < result.len() ==> exists|j: int| 0 <= j < arr.len() && #[trigger] result[i] == arr[j],
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    for i in 0..arr.len() {
        if is_even(arr[i]) {
            result.push(arr[i]);
        }
    }
    result
}
// </vc-code>

}
fn main() {}