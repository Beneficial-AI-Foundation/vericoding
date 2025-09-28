// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(a: Seq<i32>, key: i32) -> nat {
    a.filter(|x: i32| x == key).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma to prove property of count_occurrences */
proof fn lemma_count_occurrences_push(s: Seq<i32>, elem: i32, key: i32)
    ensures
        count_occurrences(s.push(elem), key) ==
            if elem == key {
                count_occurrences(s, key) + 1
            } else {
                count_occurrences(s, key)
            },
{
}
// </vc-helpers>

// <vc-spec>
fn only_once(a: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> count_occurrences(a@, key) == 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added helper lemma call and post-loop assertion */
    let mut i: usize = 0;
    let mut count: u64 = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count == count_occurrences(a@.subrange(0, i as int), key),
        decreases a.len() - i,
    {
        if a[i] == key {
            count = count + 1;
        }

        proof {
            lemma_count_occurrences_push(a@.subrange(0, i as int), a@[i as int], key);
        }

        i = i + 1;
    }

    assert(a@.subrange(0, a.len() as int) == a@);

    let result = count == 1;
    result
}
// </vc-code>

}
fn main() {}