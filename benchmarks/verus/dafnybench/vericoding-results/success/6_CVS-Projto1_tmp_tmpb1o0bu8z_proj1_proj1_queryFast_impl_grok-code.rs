use vstd::prelude::*;

verus! {

// Exercise 1.a)
spec fn sum(a: Seq<int>, i: int, j: int) -> int
    decreases j - i
{
    if i == j {
        0
    } else if i < j && j-1 < a.len() {
        a[j-1] + sum(a, i, j-1)
    } else {
        0  // default case
    }
}

// Exercise 1.b)

// Exercise 1.c)

spec fn is_prefix_sum_for(a: Seq<int>, c: Seq<int>) -> bool {
    a.len() + 1 == c.len()
    && c[0] == 0
    && forall |j: int| #![auto] 1 <= j <= a.len() ==> c[j] == sum(a, 0, j)
}

// Exercise 2.
pub enum List<T> {
    Nil,
    Cons { head: T, tail: Box<List<T>> }
}

fn from_array<T: Copy + PartialEq>(a: &Vec<T>) -> (l: List<T>)
    requires a.len() > 0
    ensures forall |j: int| #![auto] 0 <= j < a.len() ==> mem(a@[j], &l)
{
    assume(false);
    List::Nil
}

spec fn mem<T: PartialEq>(x: T, l: &List<T>) -> bool
    decreases l
{
    match l {
        List::Nil => false,
        List::Cons { head: y, tail: r } => if x == *y { true } else { mem(x, r) }
    }
}

// <vc-helpers>
proof fn sum_range(a: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= a.len()
    ensures sum(a, 0, j) - sum(a, 0, i) == sum(a, i, j)
    decreases j - i
{
    if i == j {
        // Base case: both sides are 0
    } else {
        // Recursive case
        assert(i < j);
        sum_range(a, i, j-1);
        assert(sum(a, i, j-1) == sum(a, 0, j-1) - sum(a, 0, i));
        assert(sum(a, 0, j) == a[j-1] + sum(a, 0, j-1));
        assert(sum(a, i, j) == a[j-1] + sum(a, i, j-1));
    }
}
// </vc-helpers>

// <vc-spec>
proof fn query_fast(a: Seq<int>, c: Seq<int>, i: int, j: int) -> (r: int)
    requires 
        is_prefix_sum_for(a, c) && 0 <= i <= j <= a.len() < c.len()
    ensures r == sum(a, i, j)
// </vc-spec>
// <vc-code>
{
    let r: int = c[j] - c[i];
    assert(is_prefix_sum_for(a, c));
    assert(forall |k: int| #![auto] 0 <= k <= a.len() ==> c[k] == sum(a, 0, k));
    assert(c[i] == sum(a, 0, i));
    assert(c[j] == sum(a, 0, j));
    sum_range(a, i, j);
    assert(r == sum(a, 0, j) - sum(a, 0, i) == sum(a, i, j));
    r
}
// </vc-code>

fn main() {}

}