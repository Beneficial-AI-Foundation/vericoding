// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn number_to_name(n: int) -> &'static str
{
    if n == 1 { "One" }
    else if n == 2 { "Two" }
    else if n == 3 { "Three" }
    else if n == 4 { "Four" }
    else if n == 5 { "Five" }
    else if n == 6 { "Six" }
    else if n == 7 { "Seven" }
    else if n == 8 { "Eight" }
    else { "Nine" }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Relates Vec length and its Seq view length */
proof fn vec_len_as_int_equals_view_len<T>(v: &Vec<T>)
    ensures
        v@.len() == v.len() as int,
{
}

/* helper modified by LLM (iteration 2): Bounds for reversed index (int domain) */
proof fn rev_index_bounds(k: int, n: int)
    requires
        0 <= k < n,
    ensures
        0 <= n - 1 - k,
        n - 1 - k < n,
{
}
// </vc-helpers>

// <vc-spec>
fn reverse(s: Vec<i8>) -> (rev: Vec<i8>)
    ensures 
        rev.len() == s.len(),
        forall|k: int| 0 <= k < s.len() ==> rev[k] as int == s@[s.len() - 1 - k] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Implement reverse with loop, maintain invariants, and prove index bounds */
    let n = s.len();
    proof { vec_len_as_int_equals_view_len(&s); }
    let mut r: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            r.len() == i,
            i <= n,
            s@.len() == n as int,
            forall|k: int| 0 <= k < i as int ==> r@[k] as int == s@[n as int - 1 - k] as int,
        decreases n as int - i as int
    {
        let idx = n - 1 - i;
        assert(idx < n);
        r.push(s[idx]);
        i += 1;
    }
    r
}
// </vc-code>


}

fn main() {}