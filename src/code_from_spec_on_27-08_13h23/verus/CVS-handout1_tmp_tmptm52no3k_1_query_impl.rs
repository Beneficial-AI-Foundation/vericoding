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
spec fn prefix_sum(a: &[int], k: int) -> int
    recommends 0 <= k <= a.len()
    decreases k when 0 <= k <= a.len()
{
    if k == 0 { 0 }
    else { prefix_sum(a, k - 1) + a[k - 1] }
}

proof fn prefix_sum_correct(a: &[int], k: int)
    requires 0 <= k <= a.len()
    ensures prefix_sum(a, k) == sum(a, 0, k)
    decreases k
{
    if k == 0 {
        assert(sum(a, 0, 0) == 0);
        assert(prefix_sum(a, 0) == 0);
    } else {
        prefix_sum_correct(a, k - 1);
        assert(prefix_sum(a, k) == prefix_sum(a, k - 1) + a[k - 1]);
        assert(sum(a, 0, k) == sum(a, 0, k - 1) + a[k - 1]);
    }
}

proof fn sum_split(a: &[int], i: int, j: int, k: int)
    requires 0 <= i <= k <= j <= a.len()
    ensures sum(a, i, j) == sum(a, i, k) + sum(a, k, j)
    decreases j - i
{
    if i == j {
        assert(sum(a, i, j) == 0);
        assert(sum(a, i, k) == 0);
        assert(sum(a, k, j) == 0);
    } else if i == k {
        assert(sum(a, i, k) == 0);
        assert(sum(a, i, j) == sum(a, k, j));
    } else if k == j {
        assert(sum(a, k, j) == 0);
        assert(sum(a, i, j) == sum(a, i, k));
    } else {
        assert(sum(a, i, j) == a[i] + sum(a, i + 1, j));
        sum_split(a, i + 1, j, k);
        assert(sum(a, i + 1, j) == sum(a, i + 1, k) + sum(a, k, j));
        assert(sum(a, i, j) == a[i] + sum(a, i + 1, k) + sum(a, k, j));
        assert(sum(a, i, k) == a[i] + sum(a, i + 1, k));
        assert(sum(a, i, j) == sum(a, i, k) + sum(a, k, j));
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn query(a: &[int], i: usize, j: usize) -> (res: i64)
    requires 0 <= i <= j <= a.len()
    ensures res == sum(a, i as int, j as int)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn query(a: &[int], i: usize, j: usize) -> (res: i64)
    requires 0 <= i <= j <= a.len()
    ensures res == sum(a, i as int, j as int)
{
    let mut sum: i64 = 0;
    let mut k: usize = i;
    while k < j
        invariant 
            i <= k <= j,
            sum == sum(a, i as int, k as int)
    {
        sum = sum + a[k] as i64;
        k = k + 1;
    }
    sum
}
// </vc-code>

fn main() {
}

}