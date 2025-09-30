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
proof fn lemma_sum_self_zero(a: Seq<int>, i: int)
    requires 0 <= i <= a.len()
    ensures sum(a, i, i) == 0
{
    reveal(sum);
    assert(sum(a, i, i) == 0);
}

proof fn lemma_sum_telescope(a: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= a.len()
    ensures sum(a, 0, j) == sum(a, 0, i) + sum(a, i, j)
    decreases j - i
{
    if i == j {
        lemma_sum_self_zero(a, i);
        assert(sum(a, 0, j) == sum(a, 0, i));
    } else {
        assert(i < j);
        assert(0 < j);
        assert(j - 1 < a.len());
        reveal(sum);
        assert(sum(a, 0, j) == a[j-1] + sum(a, 0, j-1));
        assert(sum(a, i, j) == a[j-1] + sum(a, i, j-1));
        assert(0 <= i <= j - 1 <= a.len());
        lemma_sum_telescope(a, i, j - 1);
        assert(sum(a, 0, j-1) == sum(a, 0, i) + sum(a, i, j-1));
        assert(sum(a, 0, j) == a[j-1] + (sum(a, 0, i) + sum(a, i, j-1)));
        assert(sum(a, 0, j) == sum(a, 0, i) + (a[j-1] + sum(a, i, j-1)));
        assert(sum(a, 0, j) == sum(a, 0, i) + sum(a, i, j));
    }
}

proof fn lemma_c_matches_sum0(a: Seq<int>, c: Seq<int>, k: int)
    requires is_prefix_sum_for(a, c) && 0 <= k <= a.len()
    ensures c[k] == sum(a, 0, k)
{
    if k == 0 {
        assert(c[0] == 0);
        lemma_sum_self_zero(a, 0);
        assert(sum(a, 0, 0) == 0);
        assert(c[0] == sum(a, 0, 0));
    } else {
        assert(1 <= k <= a.len());
        assert(c[k] == sum(a, 0, k)) by {
            assert(1 <= k <= a.len());
        }
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
    let res = c[j] - c[i];
    lemma_c_matches_sum0(a, c, j);
    lemma_c_matches_sum0(a, c, i);
    let s0j = sum(a, 0, j);
    let s0i = sum(a, 0, i);
    let sij_wanted = sum(a, i, j);
    lemma_sum_telescope(a, i, j);
    assert(res == s0j - s0i);
    assert(s0j == s0i + sij_wanted);
    assert(res == (s0i + sij_wanted) - s0i);
    assert(res == sij_wanted);
    res
}
// </vc-code>

fn main() {}

}