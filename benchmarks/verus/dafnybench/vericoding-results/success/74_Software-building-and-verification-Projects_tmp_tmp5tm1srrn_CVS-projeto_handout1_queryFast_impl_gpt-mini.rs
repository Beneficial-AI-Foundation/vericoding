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
proof fn sum_range_from_prefix(a: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= a.len()
    ensures sum(a, i, j) == sum(a, 0, j) - sum(a, 0, i)
    decreases j - i
{
    if i == j {
        // sum(a, i, i) == 0 and sum(a,0,i)-sum(a,0,i) == 0
        assert(sum(a, i, j) == 0);
        assert(sum(a, 0, j) - sum(a, 0, i) == 0);
    } else {
        // j > i
        // use recursive hypothesis for (i, j-1)
        sum_range_from_prefix(a, i, j - 1);
        // unfold definitions
        assert(sum(a, i, j) == a[j - 1] + sum(a, i, j - 1));
        assert(sum(a, 0, j) == a[j - 1] + sum(a, 0, j - 1));
        // replace sum(a, i, j-1) with sum(a,0,j-1)-sum(a,0,i)
        assert(sum(a, i, j - 1) == sum(a, 0, j - 1) - sum(a, 0, i));
        // combine equalities
        assert(a[j - 1] + sum(a, i, j - 1) == a[j - 1] + (sum(a, 0, j - 1) - sum(a, 0, i)));
        assert(a[j - 1] + (sum(a, 0, j - 1) - sum(a, 0, i)) == (a[j - 1] + sum(a, 0, j - 1)) - sum(a, 0, i));
        assert((a[j - 1] + sum(a, 0, j - 1)) - sum(a, 0, i) == sum(a, 0, j) - sum(a, 0, i));
        // conclude
        assert(sum(a, i, j) == sum(a, 0, j) - sum(a, 0, i));
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
    sum_range_from_prefix(a, i, j);
    assert(c[j] == sum(a, 0, j));
    assert(c[i] == sum(a, 0, i));
    assert(c[j] - c[i] == sum(a, i, j));
    c[j] - c[i]
}
// </vc-code>

fn main() {
}

}