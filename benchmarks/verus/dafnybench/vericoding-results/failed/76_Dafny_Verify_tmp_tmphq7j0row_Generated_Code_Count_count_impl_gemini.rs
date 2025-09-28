// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_count(v: int, a: Seq<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        if a[n-1] == v {
            has_count(v, a, (n-1) as nat) + 1
        } else {
            has_count(v, a, (n-1) as nat)
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): kept existing helper to unfold has_count definition */
proof fn has_count_unfold(v: int, a: Seq<int>, i: int)
    requires 0 <= i < a.len()
    ensures
        has_count(v, a, (i + 1) as nat) ==
            if a[i] == v {
                has_count(v, a, i as nat) + 1
            } else {
                has_count(v, a, i as nat)
            },
{}
// </vc-helpers>

// <vc-spec>
fn count(v: i32, a: &[i32], n: usize) -> (r: i32)
    requires n <= a.len()
    ensures n <= a.len() ==> has_count(v as int, a@.map_values(|x: i32| x as int), n as nat) == r as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed mismatched types and cast from nat to i32 */
    let mut i: usize = 0;
    let mut c: nat = 0 as nat;
    while i < n
        invariant
            n <= a.len(),
            i <= n,
            has_count(v as int, a@.map_values(|x: i32| x as int), i as nat) == c as int,
        decreases n - i
    {
        proof {
            let a_seq = a@.map_values(|x: i32| x as int);
            assert(i < a.len()) by {
              assert(i < n);
              assert(n <= a.len());
            };
            has_count_unfold(v as int, a_seq, i as int);
        }

        if a[i] == v {
            c = c + (1 as nat);
        }
        
        i = i + 1;
    }
    c as int as i32
}
// </vc-code>

}
fn main() {}