use vstd::prelude::*;

verus! {

/*                                      Cumulative Sums over Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes         57854
*/



//(a)

spec fn sum(a: Seq<int>, i: int, j: int) -> int
    decreases j - i
{
    if i >= j { 
        0 
    } else { 
        a[i] + sum(a, i + 1, j) 
    }
}



//(b)




//(c)

spec fn is_prefix_sum_for(a: Seq<int>, c: Seq<int>) -> bool
{
    &&& a.len() + 1 == c.len() 
    &&& c.len() > 0 
    &&& c[0] == 0
    &&& forall|i: int| 0 <= i < a.len() ==> c[i + 1] == c[i] + a[i]
}

// <vc-helpers>
#[verifier(nonlinear)]
proof fn lemma_prefix_sum_sum_equivalent(a: Seq<int>, c: Seq<int>, i: int, j: int)
    requires
        is_prefix_sum_for(a, c),
        0 <= i <= j <= a.len(),
    ensures
        sum(a, i, j) == c[j] - c[i],
    decreases j - i
{
    if i == j {
        assert(sum(a, i, j) == 0);
        assert(c[j] - c[i] == 0);
    } else {
        assert(is_prefix_sum_for(a, c));
        assert(c[i + 1] == c[i] + a[i]); // from is_prefix_sum_for
        lemma_prefix_sum_sum_equivalent(a, c, i + 1, j);
        assert(sum(a, i + 1, j) == c[j] - c[i + 1]);
        assert(sum(a, i, j) == a[i] + sum(a, i + 1, j));
        assert(a[i] + (c[j] - c[i + 1]) == a[i] + (c[j] - (c[i] + a[i])));
        assert(a[i] + (c[j] - (c[i] + a[i])) == a[i] + c[j] - c[i] - a[i]);
        assert(a[i] + c[j] - c[i] - a[i] == c[j] - c[i]);
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
    proof {
        let a_seq = a@.map(|_i, x| x as int);
        let c_seq = c@.map(|_i, x| x as int);
        lemma_prefix_sum_sum_equivalent(a_seq, c_seq, i as int, j as int);
    }
    c@[j as int] as i32 - c@[i as int] as i32
}
// </vc-code>

fn main() {}

}