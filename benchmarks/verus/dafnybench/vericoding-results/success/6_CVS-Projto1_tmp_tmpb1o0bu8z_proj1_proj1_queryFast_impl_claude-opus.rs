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
proof fn sum_split(a: Seq<int>, i: int, j: int, k: int)
    requires 0 <= i <= k <= j <= a.len()
    ensures sum(a, i, j) == sum(a, i, k) + sum(a, k, j)
    decreases j - k
{
    if k == j {
        assert(sum(a, k, j) == 0);
        assert(sum(a, i, j) == sum(a, i, k));
    } else {
        assert(k < j);
        assert(j - 1 < a.len());
        assert(sum(a, k, j) == a[j-1] + sum(a, k, j-1));
        sum_split(a, i, j-1, k);
        assert(sum(a, i, j-1) == sum(a, i, k) + sum(a, k, j-1));
        assert(sum(a, i, j) == a[j-1] + sum(a, i, j-1));
        assert(sum(a, i, j) == a[j-1] + sum(a, i, k) + sum(a, k, j-1));
        assert(sum(a, i, j) == sum(a, i, k) + (a[j-1] + sum(a, k, j-1)));
        assert(sum(a, i, j) == sum(a, i, k) + sum(a, k, j));
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
    // From is_prefix_sum_for, we know:
    // - c[0] == 0
    // - forall j: 1 <= j <= a.len() ==> c[j] == sum(a, 0, j)
    
    // Since 0 <= i <= j <= a.len(), we have:
    // - c[i] == sum(a, 0, i) (when i > 0)
    // - c[j] == sum(a, 0, j) (when j > 0)
    
    if i == 0 {
        if j == 0 {
            assert(sum(a, 0, 0) == 0);
            assert(c[0] == 0);
            0
        } else {
            assert(1 <= j <= a.len());
            assert(c[j] == sum(a, 0, j));
            c[j] as int
        }
    } else {
        // i > 0, so both c[i] and c[j] are defined by the prefix sum property
        assert(1 <= i <= a.len());
        assert(1 <= j <= a.len());
        assert(c[i] == sum(a, 0, i));
        assert(c[j] == sum(a, 0, j));
        
        // Use the splitting lemma
        sum_split(a, 0, j, i);
        assert(sum(a, 0, j) == sum(a, 0, i) + sum(a, i, j));
        assert(c[j] == sum(a, 0, i) + sum(a, i, j));
        assert(c[j] == c[i] + sum(a, i, j));
        assert(sum(a, i, j) == c[j] - c[i]);
        
        (c[j] - c[i]) as int
    }
}
// </vc-code>

fn main() {}

}