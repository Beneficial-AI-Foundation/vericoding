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
proof fn prefix_sum_implies_sum(a: Seq<int>, c: Seq<int>, i: int, j: int)
    requires
        is_prefix_sum_for(a, c),
        0 <= i <= j <= a.len(),
    ensures
        c[j] - c[i] == sum(a, i, j)
    decreases j - i
{
    if i == j {
        assert(sum(a, i, j) == 0);
        assert(c[j] - c[i] == 0);
    } else {
        prefix_sum_implies_sum(a, c, i + 1, j);
        assert(c[i + 1] == c[i] + a[i]) by {
            assert(0 <= i < a.len());
        };
        assert(c[j] - c[i] == (c[j] - c[i + 1]) + a[i]);
        assert(c[j] - c[i + 1] == sum(a, i + 1, j));
        assert(sum(a, i, j) == a[i] + sum(a, i + 1, j));
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn queryFast(a: &[i32], c: &[i32], i: i32, j: i32) -> (r: i32)
    requires a.len() + 1 == c.len() && c.len() > 0 && c@[0] == 0,
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a@.map(|_i, x| x as int), c@.map(|_i, x| x as int))
    ensures r as int == sum(a@.map(|_i, x| x as int), i as int, j as int)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn queryFast(a: &[i32], c: &[i32], i: i32, j: i32) -> (r: i32)
    requires
        a.len() + 1 == c.len() && c.len() > 0 && c@[0] == 0,
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a@.map(|_i, x| x as int), c@.map(|_i, x| x as int))
    ensures
        r as int == sum(a@.map(|_i, x| x as int), i as int, j as int)
{
    proof {
        prefix_sum_implies_sum(
            a@.map(|_i, x| x as int),
            c@.map(|_i, x| x as int),
            i as int,
            j as int
        );
    }
    (c[j as usize] - c[i as usize])
}
// </vc-code>

fn main() {}

}