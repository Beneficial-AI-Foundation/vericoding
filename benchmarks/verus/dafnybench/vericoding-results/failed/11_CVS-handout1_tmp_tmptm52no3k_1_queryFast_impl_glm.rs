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
proof fn lemma_prefix_sum_property(a: Seq<int>, c: Seq<int>, i: int, j: int)
    requires
        is_prefix_sum_for(a, c),
        0 <= i <= j <= a.len(),
    ensures
        sum(a, i, j) == c[j] - c[i]
    decreases j - i
{
    if i >= j {
        assert(sum(a, i, j) == 0);
        assert(c[j] - c[i] == 0);
    } else {
        assert(sum(a, i, j) == a[i] + sum(a, i+1, j));
        assert(c[i+1] == c[i] + a[i]);
        lemma_prefix_sum_property(a, c, i+1, j);
        assert(c[j] - c[i] == (c[j] - c[i+1]) + (c[i+1] - c[i]));
        assert(c[j] - c[i] == sum(a, i+1, j) + a[i]);
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
    let result = c[j as usize] - c[i as usize];
    proof {
        let a_int = a@.map(|_i, x| x as int);
        let c_int = c@.map(|_i, x| x as int);
        lemma_prefix_sum_property(a_int, c_int, i as int, j as int);
        assert(result as int == c_int[j as int] - c_int[i as int]);
    }
    result
}
// </vc-code>

fn main() {}

}