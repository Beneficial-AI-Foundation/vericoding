// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(a: Seq<i32>, key: i32) -> nat {
    a.filter(|x: i32| x == key).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added verified count_occurrences_vec function */
fn count_occurrences_vec(a: &Vec<i32>, key: i32) -> (count: usize)
    ensures count as int == count_occurrences(a@, key)
{
    let mut c: usize = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            c as int == count_occurrences(a@.subrange(0, i as int), key),
        decreases a@.len() - (i as nat)
    {
        if a[i] == key {
            c += 1;
        }
        i += 1;
    }
    c
}
// </vc-helpers>

// <vc-spec>
fn only_once(a: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> count_occurrences(a@, key) == 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): use helper function to count occurrences */
    let count = count_occurrences_vec(a, key);
    count == 1
}
// </vc-code>

}
fn main() {}