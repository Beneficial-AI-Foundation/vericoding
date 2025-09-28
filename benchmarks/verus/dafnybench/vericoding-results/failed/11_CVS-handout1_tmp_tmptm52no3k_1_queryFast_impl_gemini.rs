// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(a: Seq<int>, i: int, j: int) -> int
    decreases j - i
{
    if i >= j { 
        0 
    } else { 
        a[i] + sum(a, i + 1, j) 
    }
}

spec fn is_prefix_sum_for(a: Seq<int>, c: Seq<int>) -> bool
{
    &&& a.len() + 1 == c.len() 
    &&& c.len() > 0 
    &&& c[0] == 0
    &&& forall|i: int| 0 <= i < a.len() ==> c[i + 1] == c[i] + a[i]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): add assert to prove connection in inductive step */
proof fn lemma_prefix_sum_is_sum_from_zero(a: Seq<int>, c: Seq<int>, k: int)
    requires
        is_prefix_sum_for(a, c),
        0 <= k <= a.len(),
    ensures
        c[k] == sum(a, 0, k),
    decreases k
{
    if k > 0 {
        lemma_prefix_sum_is_sum_from_zero(a, c, k - 1);
        lemma_sum_split(a, 0, k - 1, k);
        assert(c[k] == c[k-1] + a[k-1]);
    }
}

proof fn lemma_sum_split(a: Seq<int>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= a.len(),
    ensures
        sum(a, i, k) == sum(a, i, j) + sum(a, j, k),
    decreases k - i
{
    if i < j {
        lemma_sum_split(a, i + 1, j, k);
    }
}
// </vc-helpers>

// <vc-spec>
fn queryFast(a: &[i32], c: &[i32], i: i32, j: i32) -> (r: i32)
    requires a.len() + 1 == c.len() && c.len() > 0 && c@[0] == 0,
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a@.map(|_i, x| x as int), c@.map(|_i, x| x as int))
    ensures r as int == sum(a@.map(|_i, x| x as int), i as int, j as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): use proof block to establish mathematical equality */
    proof {
        let a_spec = a@.map(|_i, x| x as int);
        let c_spec = c@.map(|_i, x| x as int);
        let i_int = i as int;
        let j_int = j as int;

        lemma_prefix_sum_is_sum_from_zero(a_spec, c_spec, j_int);
        lemma_prefix_sum_is_sum_from_zero(a_spec, c_spec, i_int);
        
        lemma_sum_split(a_spec, 0, i_int, j_int);

        assert(sum(a_spec, 0, j_int) == sum(a_spec, 0, i_int) + sum(a_spec, i_int, j_int)) by {
            // This is the ensures clause of lemma_sum_split
        }
        assert(c_spec[j_int] == c_spec[i_int] + sum(a_spec, i_int, j_int)) by {
            // Established by the lemmas above
        }
    }
    
    (c[j as usize] - c[i as usize])
}
// </vc-code>

}
fn main() {}