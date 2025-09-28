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
proof fn slice_map_index_is(c: &[i32], k: usize)
    requires k < c.len()
    ensures c@.map(|_i: usize, x: i32| x as int)@[k as int] == c[k] as int
{
    // relation between slice indexing and slice-to-seq representation
    assert(c@[k as int] == c[k]);
    // relation between map and element casting
    assert(c@.map(|_i: usize, x: i32| x as int)@[k as int] == (c@[k as int] as int));
    assert((c@[k as int] as int) == c[k] as int);
}

proof fn lemma_prefix_sum_sum(a: Seq<int>, c: Seq<int>, i: int, j: int)
    requires is_prefix_sum_for(a, c) && 0 <= i && i <= j && j <= a.len() as int
    ensures sum(a, i, j) == c[j] - c[i]
    decreases j - i
{
    if i >= j {
        // i == j
        assert(i == j);
        assert(sum(a, i, j) == 0);
        assert(c[j] - c[i] == 0);
    } else {
        // sum(a,i,j) = a[i] + sum(a, i+1, j)
        assert(sum(a, i, j) == a[i] + sum(a, i + 1, j));
        // from prefix property: c[i+1] == c[i] + a[i]
        assert(c[i + 1] == c[i] + a[i]);
        // apply inductive hypothesis to sum(a, i+1, j)
        lemma_prefix_sum_sum(a, c, i + 1, j);
        assert(sum(a, i + 1, j) == c[j] - c[i + 1]);
        // combine
        assert(a[i] + (c[j] - c[i + 1]) == c[j] - c[i]);
        assert(sum(a, i, j) == c[j] - c[i]);
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
    let res_i32: i32 = c[j as usize] - c[i as usize];
    proof {
        // prove non-negativity needed for casts
        assert(0 <= i);
        assert(0 <= j);

        // prove i and j fit within a.len()
        assert((i as usize) <= a.len());
        assert((j as usize) <= a.len());

        // relate c.len() to a.len() from the precondition a.len() + 1 == c.len()
        assert(c.len() == a.len() + 1);

        // hence i and j are valid indices into c (strictly less than c.len())
        assert((i as usize) < c.len());
        assert((j as usize) < c.len());

        // relate concrete slice elements to the abstract mapped sequences
        slice_map_index_is(c, j as usize);
        slice_map_index_is(c, i as usize);

        // use prefix-sum lemma on the abstract sequences
        lemma_prefix_sum_sum(
            a@.map(|_k: usize, x: i32| x as int),
            c@.map(|_k: usize, x: i32| x as int),
            i as int,
            j as int
        );

        // connect the concrete subtraction to the abstract difference
        assert((res_i32 as int) == (c[j as usize] as int) - (c[i as usize] as int));
        assert((c[j as usize] as int) == c@.map(|_k: usize, x: i32| x as int)@[j as int]);
        assert((c[i as usize] as int) == c@.map(|_k: usize, x: i32| x as int)@[i as int]);
        assert((res_i32 as int) == c@.map(|_k: usize, x: i32| x as int)@[j as int] - c@.map(|_k: usize, x: i32| x as int)@[i as int]);
        assert((res_i32 as int) == sum(a@.map(|_k: usize, x: i32| x as int), i as int, j as int));
    }
    res_i32
}
// </vc-code>

fn main() {}

}