// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(a: Seq<i32>, key: i32) -> nat {
    a.filter(|x: i32| x == key).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversions and nat arithmetic */
proof fn lemma_count_occurrences_empty(key: i32) 
    ensures count_occurrences(Seq::empty(), key) == 0 
{
}

proof fn lemma_count_occurrences_cons(a: Seq<i32>, key: i32, x: i32) 
    ensures count_occurrences(a.push(x), key) == count_occurrences(a, key) + (if x == key { 1 } else { 0 })
{
    if a.len() == 0 {
        lemma_count_occurrences_empty(key);
    } else {
        let subseq = a.subrange(0, a.len() as int - 1);
        let last = a[a.len() as int - 1];
        lemma_count_occurrences_cons(subseq, key, last);
    }
}

proof fn lemma_count_occurrences_snoc(a: Seq<i32>, key: i32, x: i32) 
    ensures count_occurrences(a.insert(a.len() as int, x), key) == count_occurrences(a, key) + (if x == key { 1 } else { 0 })
{
    lemma_count_occurrences_cons(a, key, x);
}

proof fn lemma_count_occurrences_split(a: Seq<i32>, key: i32, i: int) 
    requires 0 <= i <= a.len() as int
    ensures count_occurrences(a, key) == count_occurrences(a.subrange(0, i), key) + count_occurrences(a.subrange(i, a.len() as int), key)
    decreases a.len() as int - i
{
    if i == a.len() as int {
    } else {
        let x = a[i];
        lemma_count_occurrences_split(a.subrange(i + 1, a.len() as int), key, 0);
        lemma_count_occurrences_cons(a.subrange(0, i), key, x);
    }
}
// </vc-helpers>

// <vc-spec>
fn only_once(a: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> count_occurrences(a@, key) == 1,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed nat arithmetic and usize/int conversions */
{
    let mut count: int = 0;
    let mut seen_once = false;
    let mut i: usize = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            count == count_occurrences(a@.subrange(0, i as int), key) as int,
            seen_once <==> count == 1
        decreases a.len() - i
    {
        if a[i] == key {
            count = count + 1;
            seen_once = count == 1;
        }
        i = i + 1;
    }
    seen_once
}
// </vc-code>

}
fn main() {}