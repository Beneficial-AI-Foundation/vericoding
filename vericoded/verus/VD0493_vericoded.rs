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
proof fn open_is_prefix_sum_for(a: Seq<int>, c: Seq<int>)
    requires is_prefix_sum_for(a, c)
    ensures a.len() + 1 == c.len(),
            forall|i:int| 0 <= i <= a.len() ==> c[i] == sum(a, 0, i)
{ }

proof fn sum_prefix_difference(a: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= a.len()
    ensures sum(a, i, j) == sum(a, 0, j) - sum(a, 0, i)
    decreases j - i
{
    if i == j {
        assert(sum(a, i, j) == 0);
        assert(sum(a, 0, j) == sum(a, 0, i));
        assert(sum(a, 0, j) - sum(a, 0, i) == 0);
    } else {
        assert(i < j);
        sum_prefix_difference(a, i, j - 1);
        assert(0 <= 0 <= j <= a.len());
        assert(0 < j);
        assert(0 <= j - 1 < a.len());
        assert(sum(a, 0, j) == a[j - 1] + sum(a, 0, j - 1));
        assert(sum(a, i, j) == a[j - 1] + sum(a, i, j - 1));
        assert(sum(a, i, j) == a[j - 1] + (sum(a, 0, j - 1) - sum(a, 0, i)));
        assert(sum(a, i, j) == (a[j - 1] + sum(a, 0, j - 1)) - sum(a, 0, i));
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
    open_is_prefix_sum_for(a, c);
    assert(0 <= i <= a.len());
    assert(0 <= j <= a.len());
    assert(0 <= i && i < c.len());
    assert(0 <= j && j < c.len());
    let r = c[j] - c[i];
    assert(c[j] == sum(a, 0, j)) by {
        assert(forall|k:int| 0 <= k <= a.len() ==> #[trigger] c[k] == sum(a, 0, k));
    }
    assert(c[i] == sum(a, 0, i)) by {
        assert(forall|k:int| 0 <= k <= a.len() ==> #[trigger] c[k] == sum(a, 0, k));
    }
    sum_prefix_difference(a, i, j);
    assert(r == sum(a, 0, j) - sum(a, 0, i));
    assert(r == sum(a, i, j));
    r
}
// </vc-code>

fn main() {
}

}