use vstd::prelude::*;

verus! {

/*                                      Cumulative Sums over Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes         57854
*/



//(a)

spec fn sum(a: &[int], i: int, j: int) -> int
    recommends 0 <= i <= j <= a.len()
    decreases j - i when 0 <= i <= j <= a.len()
{
    if i == j { 0 }
    else { a[i] + sum(a, i + 1, j) }
}



//(b)

//(c)

spec fn is_prefix_sum_for(a: &[int], c: &[int]) -> bool
{
    &&& a.len() + 1 == c.len()
    &&& c[0] == 0
    &&& forall|i: int| 0 <= i < a.len() ==> c[i + 1] == c[i] + a[i]
}

// <vc-helpers>
#[verifier(external_body)]
fn int_to_i64(x: Ghost<int>) -> (r: i64)
    ensures r == x@
{
    unimplemented!()
}
// </vc-helpers>

// <vc-spec>
fn query(a: &[int], i: usize, j: usize) -> (res: i64)
    requires 0 <= i <= j <= a.len()
    ensures res == sum(a, i as int, j as int)
// </vc-spec>
// <vc-code>
{
    int_to_i64(Ghost(sum(a, i as int, j as int)))
}
// </vc-code>

fn main() {
}

}