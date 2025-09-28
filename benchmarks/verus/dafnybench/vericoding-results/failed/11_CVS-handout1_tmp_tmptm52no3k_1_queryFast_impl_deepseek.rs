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
proof fn lemma_prefix_sum_properties(a: Seq<int>, c: Seq<int>, i: int, j: int)
    requires
        is_prefix_sum_for(a, c),
        0 <= i <= j <= a.len()
    ensures
        sum(a, i, j) == c[j] - c[i]
    decreases j - i
{
    if i < j {
        lemma_prefix_sum_properties(a, c, i + 1, j);
        assert(c[i + 1] == c[i] + a[i]);
        assert(sum(a, i, j) == a[i] + sum(a, i + 1, j));
    }
}

proof fn lemma_is_prefix_sum_implies_invariants(a: Seq<int>, c: Seq<int>)
    requires
        is_prefix_sum_for(a, c)
    ensures
        a.len() + 1 == c.len(),
        c.len() > 0,
        c[0] == 0,
        forall|k: int| 0 <= k < a.len() ==> c[k + 1] == c[k] + a[k]
{
}

proof fn lemma_len_cast_valid(a: &[i32], i: i32, j: i32)
    requires
        0 <= i <= j <= a.len() as i32
    ensures
        i as usize <= a.len(),
        j as usize <= a.len()
{
    assert(a.len() as i32 <= i32::MAX);
}

proof fn lemma_safe_cast(a: &[i32], c: &[i32], i: i32, j: i32)
    requires
        0 <= i <= j <= a.len() as i32,
        is_prefix_sum_for(a@.map(|_i, x| x as int), c@.map(|_i, x| x as int))
    ensures
        i as usize <= a.len(),
        j as usize <= a.len(),
        (c[j as usize] as int) >= (c[i as usize] as int)
{
    let a_seq = a@.map(|_i, x| x as int);
    let c_seq = c@.map(|_i, x| x as int);
    lemma_is_prefix_sum_implies_invariants(a_seq, c_seq);
    lemma_prefix_sum_properties(a_seq, c_seq, i as int, j as int);
    assert(sum(a_seq, i as int, j as int) >= 0);
    assert(c_seq[j as int] >= c_seq[i as int]);
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
        lemma_len_cast_valid(a, i, j);
        lemma_safe_cast(a, c, i, j);
    }
    assert(0 <= i && i <= j && j <= a.len() as i32);
    assert(i as usize <= a.len());
    assert(j as usize <= a.len());
    assert((c[j as usize] as int) >= (c[i as usize] as int));
    let result = c[j as usize] - c[i as usize];
    result
}
// </vc-code>

fn main() {}

}