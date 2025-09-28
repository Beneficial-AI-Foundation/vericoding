use vstd::prelude::*;

verus! {

// 1 a)

// [ai, aj[
spec fn sum(a: Seq<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= a.len()
    decreases j - i
    when 0 <= i <= j <= a.len()
{
    if i == j { 0 }
    else { a[j-1] + sum(a, i, j-1) }
}

// 1 b)

// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]

spec fn is_prefix_sum_for(a: Seq<int>, c: Seq<int>) -> bool
{
    a.len() + 1 == c.len() && 
    forall|i: int| #![auto] 0 <= i <= a.len() ==> c[i] == sum(a, 0, i)
}

// <vc-helpers>
spec fn sum_0_to_k(a: Seq<int>, k: int) -> int
    recommends 0 <= k <= a.len()
{
    sum(a, 0, k)
}

proof fn lemma_prefix_sum(a: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= a.len()
    ensures sum(a, 0, j) - sum(a, 0, i) == sum(a, i, j)
    decreases j - i
{
    if i == j {
        // sum(a, i, j) = 0, sum(0,j) - sum(0,i) = 0 - 0 = 0
    } else {
        // sum(a, i, j) = a[j-1] + sum(a, i, j-1)
        // sum(0,j) - sum(0,i) = (a[j-1] + sum(0,j-1)) - sum(0,i)
        //                    = (a[j-1] + sum(0,j-1) - sum(0,i))
        // and by induction, sum(0,j-1) - sum(0,i) == sum(a,i,j-1)
        // so a[j-1] + sum(a,i,j-1) == sum(a,i,j)
        lemma_prefix_sum(a, i, j-1);
        assert(sum(a, 0, j-1) - sum(a, 0, i) == sum(a, i, j-1));
    }
}
// </vc-helpers>

// <vc-spec>
proof fn queryFast(a: Seq<int>, c: Seq<int>, i: int, j: int) -> (r: int)
    requires 0 <= i <= j <= a.len(),
             is_prefix_sum_for(a, c)
    ensures r == sum(a, i, j)
// </vc-spec>
// <vc-code>
{
    lemma_prefix_sum(a, i, j);
    assert(sum(a, 0, j) == c[j]);
    assert(sum(a, 0, i) == c[i]);
    let r = c[j] - c[i];
    assert(r == sum(a, i, j));
    r
}
// </vc-code>

fn main() {
}

}