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
proof fn prefix_sum_diff(a: Seq<int>, c: Seq<int>, i: int, j: int)
    requires is_prefix_sum_for(a, c) && 0 <= i <= j <= a.len()
    ensures c[j] - c[i] == sum(a, i, j)
    decreases j - i
{
    if i == j {
        // sum(a,i,i) == 0 and c[i] - c[i] == 0
        assert(sum(a, i, j) == 0);
        assert(c[j] - c[i] == 0);
    } else {
        // i < j, so j >= 1
        // Use the prefix-sum property: c[j] == sum(a,0,j) and c[j-1] == sum(a,0,j-1)
        assert(is_prefix_sum_for(a, c));
        // From is_prefix_sum_for, for j >= 1 we have c[j] == sum(a,0,j)
        assert(c[j] == sum(a, 0, j));
        // and for j-1 (which may be 0) we have c[j-1] == sum(a,0,j-1)
        if j-1 == 0 {
            // c[0] == 0 and sum(a,0,0) == 0
            assert(c[0] == 0);
            assert(sum(a, 0, 0) == 0);
            assert(c[j-1] == sum(a, 0, j-1));
        } else {
            // j-1 >= 1, use quantified clause
            assert(c[j-1] == sum(a, 0, j-1));
        }

        // By definition of sum, since j-1 < a.len(), sum(a,0,j) == a[j-1] + sum(a,0,j-1)
        assert(sum(a, 0, j) == a[j-1] + sum(a, 0, j-1));

        // So c[j] == a[j-1] + sum(a,0,j-1)
        assert(c[j] == a[j-1] + sum(a, 0, j-1));

        // Recurse to get c[j-1] - c[i] == sum(a,i,j-1)
        prefix_sum_diff(a, c, i, j-1);

        // Now combine:
        // c[j] - c[i] == a[j-1] + (sum(a,0,j-1) - c[i])
        // but sum(a,0,j-1) == c[j-1], so this is a[j-1] + (c[j-1] - c[i])
        assert(sum(a, 0, j-1) == c[j-1]);
        assert(c[j] - c[i] == a[j-1] + (c[j-1] - c[i]));
        // and c[j-1] - c[i] == sum(a,i,j-1) by the recursive call
        assert(c[j-1] - c[i] == sum(a, i, j-1));
        // therefore c[j] - c[i] == a[j-1] + sum(a,i,j-1) == sum(a,i,j)
        assert(c[j] - c[i] == a[j-1] + sum(a, i, j-1));
        assert(c[j] - c[i] == sum(a, i, j));
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
    let r = c[j] - c[i];
    prefix_sum_diff(a, c, i, j);
    r
}
// </vc-code>

fn main() {}

}