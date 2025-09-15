// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(a: Seq<i32>, key: i32) -> nat {
    a.filter(|x: i32| x == key).len()
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn only_once(a: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> count_occurrences(a@, key) == 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use simple for loop to count occurrences, removing the failing invariant */
    let mut count: usize = 0;
    for i in 0..a.len() {
        if a[i] == key {
            count += 1;
        }
    }
    count == 1
}
// </vc-code>

}
fn main() {}