// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(a: Seq<i32>, key: i32) -> nat {
    a.filter(|x: i32| x == key).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec function computing occurrences in prefix */
spec fn count_occurrences_prefix(a: Seq<i32>, key: i32, n: nat) -> nat {
    if n == 0 {
        0
    } else {
        let prev = count_occurrences_prefix(a, key, n - 1);
        prev + (if a[((n - 1) as int)] == key { 1 } else { 0 })
    }
}

// </vc-helpers>

// <vc-spec>
fn only_once(a: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> count_occurrences(a@, key) == 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate and count occurrences, maintain invariant linking runtime count to spec */
    let mut i: usize = 0;
    let mut count: usize = 0;
    while i < a.len()
        invariant
            (count as nat) == count_occurrences_prefix(a@, key, i as nat),
            i <= a.len(),
        decreases a.len() - i
    {
        if a[i] == key {
            count = count + 1;
        }
        i += 1;
    }
    count == 1usize
}

// </vc-code>

}
fn main() {}