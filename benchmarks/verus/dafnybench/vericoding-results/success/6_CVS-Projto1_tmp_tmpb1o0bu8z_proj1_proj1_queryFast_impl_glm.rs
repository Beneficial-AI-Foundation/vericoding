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
proof fn lemma_sum_split(a: Seq<int>, i: int, k: int, j: int) 
    requires 
        0 <= i <= k <= j <= a.len()
    ensures 
        sum(a, i, j) == sum(a, i, k) + sum(a, k, j)
    decreases j - i
{
    if i == j {
        assert(sum(a, i, j) == 0);
        assert(sum(a, i, k) == 0);
        assert(sum(a, k, j) == 0);
    } else if i < j && j-1 < a.len() {
        if k == j {
            assert(sum(a, k, j) == 0);
            assert(sum(a, i, j) == a[j-1] + sum(a, i, j-1));
            assert(sum(a, i, k) == sum(a, i, j));
        } else {
            lemma_sum_split(a, i, k, j-1);
            assert(sum(a, i, j) == a[j-1] + sum(a, i, j-1));
            assert(sum(a, i, j-1) == sum(a, i, k) + sum(a, k, j-1));
            assert(sum(a, k, j) == a[j-1] + sum(a, k, j-1));
            assert(a[j-1] + sum(a, i, j-1) == a[j-1] + sum(a, i, k) + sum(a, k, j-1));
            assert(sum(a, i, j) == sum(a, i, k) + (a[j-1] + sum(a, k, j-1)));
        }
    }
}

proof fn lemma_prefix_sum_property(a: Seq<int>, c: Seq<int>, k: int)
    requires 
        is_prefix_sum_for(a, c) && 0 <= k <= a.len()
    ensures 
        sum(a, 0, k) == c[k]
    decreases k
{
    if k == 0 {
        assert(c[0] == 0);
        assert(sum(a, 0, 0) == 0);
    } else {
        lemma_prefix_sum_property(a, c, k - 1);
        assert(sum(a, 0, k) == a[k-1] + sum(a, 0, k-1));
        assert(c[k] == sum(a, 0, k) == a[k-1] + sum(a, 0, k-1));
        assert(c[k-1] == sum(a, 0, k-1));
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
    lemma_prefix_sum_property(a, c, j);
    lemma_prefix_sum_property(a, c, i);
    lemma_sum_split(a, i, j, j);
    lemma_sum_split(a, 0, i, j);
    assert(sum(a, 0, j) == sum(a, 0, i) + sum(a, i, j));
    assert(sum(a, i, j) == sum(a, 0, j) - sum(a, 0, i));
    c[j] - c[i]
}
// </vc-code>

fn main() {}

}