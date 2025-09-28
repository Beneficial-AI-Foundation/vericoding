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
proof fn sum_split(a: Seq<int>, i: int, j: int, k: int)
    requires 0 <= i <= k <= j <= a.len()
    ensures sum(a, i, j) == sum(a, i, k) + sum(a, k, j)
    decreases j - k
{
    if k == j {
        assert(sum(a, k, j) == 0);
    } else {
        sum_split(a, i, j - 1, k);
        assert(sum(a, i, j) == a[j-1] + sum(a, i, j-1));
        assert(sum(a, i, j-1) == sum(a, i, k) + sum(a, k, j-1));
        assert(sum(a, k, j) == a[j-1] + sum(a, k, j-1));
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
    // From the prefix sum property: c[j] = sum(a, 0, j) and c[i] = sum(a, 0, i)
    // We need to show that sum(a, i, j) = c[j] - c[i]
    
    // Use the helper lemma to split sum(a, 0, j) into sum(a, 0, i) + sum(a, i, j)
    sum_split(a, 0, j, i);
    assert(sum(a, 0, j) == sum(a, 0, i) + sum(a, i, j));
    
    // From is_prefix_sum_for, we know:
    assert(c[i] == sum(a, 0, i));
    assert(c[j] == sum(a, 0, j));
    
    // Therefore:
    assert(c[j] == sum(a, 0, i) + sum(a, i, j));
    assert(c[j] == c[i] + sum(a, i, j));
    assert(sum(a, i, j) == c[j] - c[i]);
    
    c[j] - c[i]
}
// </vc-code>

fn main() {
}

}