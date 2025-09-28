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
proof fn lemma_prefix_sum(a: Seq<int>, c: Seq<int>, i: int, j: int)
    requires
        is_prefix_sum_for(a, c),
        0 <= i <= j <= a.len(),
    ensures
        c[j] - c[i] == sum(a, i, j)
    decreases j - i
{
    if i == j {
        assert(c[j] == c[i]);
        assert(c[j] - c[i] == 0);
        assert(sum(a, i, j) == 0);
    } else {
        lemma_prefix_sum(a, c, i + 1, j);
        assert(c[i + 1] == c[i] + a[i]);
        assert(c[j] - c[i] == (c[j] - c[i + 1]) + a[i]);
        assert(c[j] - c[i] == sum(a, i + 1, j) + a[i]);
        assert(a[i] + sum(a, i + 1, j) == sum(a, i, j));
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
    let jj = j as usize;
    let ii = i as usize;
    let r = vstd::unchecked_math::unchecked_sub(c[jj], c[ii]);
    proof {
        let a_int = a@.map(|i, x| x as int);
        let c_int = c@.map(|i, x| x as int);
        lemma_prefix_sum(a_int, c_int, i as int, j as int);
        assert(c_int@[jj] - c_int@[ii] == sum(a_int, i as int, j as int));
        assert(c_int@[jj] as i32 as int == c_int@[jj]);
        assert(c_int@[ii] as i32 as int == c_int@[ii]);
        assert(r as int == (c@[jj] as int - c@[ii] as int));
        assert(r as int == sum(a@.map(|_i, x| x as int), i as int, j as int));
    }
    r
}
// </vc-code>

fn main() {}

}