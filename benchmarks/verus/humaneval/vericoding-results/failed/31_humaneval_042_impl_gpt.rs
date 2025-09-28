// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(l: Seq<int>) -> bool
{
    true
}

spec fn correct_output(l: Seq<int>, result: Seq<int>) -> bool
{
    result.len() == l.len() && 
    forall|i: int| 0 <= i < l.len() ==> result[i] == l[i] + 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma equating Vec view length to runtime length */
proof fn vec_len_eq_view_len<T>(v: &Vec<T>)
    ensures
        v@.len() == v.len() as int,
{
    assert(v@.len() == v.len() as int);
}

/* helper modified by LLM (iteration 5): lemma: map cast index equals cast of element */
proof fn map_cast_index_eq(s: Seq<i8>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.map(|k: int, x: i8| x as int)[i] == s[i] as int,
{
    assert(s.map(|k: int, x: i8| x as int)[i] == s[i] as int);
}
// </vc-helpers>

// <vc-spec>
fn incr_list(l: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(l@.map(|i: int, x: i8| x as int))
    ensures correct_output(l@.map(|i: int, x: i8| x as int), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement simple loop constructing result; moved spec-level reasoning into invariants to avoid parse errors */
    let n = l.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            n == l.len(),
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> (result@[j] as int) == (l@[j] as int) + 1,
        decreases n as int - i as int
    {
        let x = l[i];
        let y: i8 = x + 1;
        result.push(y);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}