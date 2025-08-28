// RUN: /compile:0

use vstd::prelude::*;

verus! {

// Predicate to check if outarr is the reverse of arr
spec fn reversed(arr: Seq<char>, outarr: Seq<char>) -> bool {
    arr.len() == outarr.len() &&
    forall|k: int| 0 <= k < arr.len() ==> outarr[k] == arr[arr.len() - 1 - k]
}

// <vc-helpers>
// Helper lemma to prove properties about reversed sequences
proof fn lemma_reversed_index(arr: Seq<char>, outarr: Seq<char>, i: int)
    requires
        arr.len() == outarr.len(),
        0 <= i < arr.len(),
        reversed(arr, outarr),
    ensures
        outarr[i] == arr[arr.len() - 1 - i]
{
    // No additional proof needed as the property is directly from the definition of reversed
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn yarra(arr: &Vec<char>) -> (outarr: Vec<char>)
    requires arr.len() > 0
    ensures outarr.len() == arr.len() && reversed(arr@, outarr@)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn yarra(arr: &Vec<char>) -> (outarr: Vec<char>)
    requires arr.len() > 0
    ensures outarr.len() == arr.len() && reversed(arr@, outarr@)
{
    let mut result: Vec<char> = Vec::new();
    let arr_len = arr.len();
    
    let mut i: usize = 0;
    while i < arr_len
        invariant
            arr_len == arr.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k] == arr@[arr_len - 1 - k]
    {
        let idx = arr_len - 1 - i;
        result.push(arr[idx]);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}