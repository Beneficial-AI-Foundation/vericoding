use vstd::prelude::*;

verus! {

//Exercicio 1.a)
spec fn sum(a: Seq<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= a.len()
    decreases j when 0 <= i <= j <= a.len()
{
    if i == j {
        0
    } else {
        a[j - 1] + sum(a, i, j - 1)
    }
}

//Exercicio 1.b)

//Exercicio 1.c)


spec fn is_prefix_sum_for(a: Seq<int>, c: Seq<int>) -> bool {
    a.len() + 1 == c.len()
    && c[0] == 0
    && forall|j: int| 1 <= j <= a.len() ==> c[j] == sum(a, 0, j)
}

///Exercicio 2.
#[derive(PartialEq, Eq)]
enum List<T> {
    Nil,
    Cons { head: T, tail: Box<List<T>> }
}

fn from_array<T: Copy>(a: &[T]) -> (l: List<T>)
    requires a.len() > 0
    ensures forall|j: int| 0 <= j < a.len() ==> mem(a@[j], l)
{
    assume(false);
    List::Nil
}

spec fn mem<T>(x: T, l: List<T>) -> bool
    decreases l
{
    match l {
        List::Nil => false,
        List::Cons { head: y, tail: r } => if x == y { true } else { mem(x, *r) }
    }
}

// <vc-helpers>
proof fn sum_rec(a: Seq<int>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= a.len(),
        0 <= k <= j - i,
    ensures
        sum(a, i, j) == sum(a, i, j - k) + sum(a, j - k, j),
    decreases k,
{
    if k > 0 {
        assert(j - k >= i) by { 
            assert(j - i >= k); 
        };
        sum_rec(a, i, j, k - 1);
        assert(sum(a, i, j) == sum(a, i, j - (k - 1)) + sum(a, j - (k - 1), j));
        assert(sum(a, i, j - (k - 1)) == sum(a, i, j - k) + a[j - k]);
        assert(sum(a, j - (k - 1), j) == a[j - 1] + sum(a, j - k, j - 1));
        assert(sum(a, j - k, j - 1) + a[j - 1] == sum(a, j - k, j));
    }
}

proof fn sum_empty(a: Seq<int>, i: int)
    requires
        0 <= i <= a.len(),
    ensures
        sum(a, i, i) == 0,
{
}

proof fn sum_single(a: Seq<int>, i: int)
    requires
        0 <= i < a.len(),
    ensures
        sum(a, i, i + 1) == a[i],
{
    assert(sum(a, i, i + 1) == a[i] + sum(a, i, i));
    sum_empty(a, i);
}

proof fn sum_append(a: Seq<int>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= a.len(),
    ensures
        sum(a, i, k) == sum(a, i, j) + sum(a, j, k),
    decreases k - j,
{
    if j < k {
        sum_append(a, i, j, k - 1);
        assert(sum(a, i, k) == a[k - 1] + sum(a, i, k - 1));
        assert(sum(a, j, k) == a[k - 1] + sum(a, j, k - 1));
        assert(sum(a, i, k - 1) == sum(a, i, j) + sum(a, j, k - 1));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn query(a: &[i32], i: usize, j: usize) -> (s: i32)
    requires 0 <= i <= j <= a.len()
    ensures s == sum(a@.map(|k, x| x as int), i as int, j as int)
// </vc-spec>
// <vc-code>
{
    let mut s: i32 = 0;
    let mut idx = i;
    let ghost mapped = a@.map(|k, x| x as int);
    while idx < j
        invariant
            i <= idx <= j,
            s as int == sum(mapped, i as int, idx as int),
        decreases j - idx,
    {
        let old_idx = idx;
        assert(i <= old_idx < j) by { assert(old_idx >= i && old_idx < j); };
        idx = idx + 1;
        proof {
            sum_single(mapped, old_idx as int);
            assert(sum(mapped, old_idx as int, idx as int) == mapped[old_idx as int]);
            sum_append(mapped, i as int, old_idx as int, idx as int);
            assert(sum(mapped, i as int, idx as int) == 
                   sum(mapped, i as int, old_idx as int) + 
                   sum(mapped, old_idx as int, idx as int));
        }
        s = s + a[old_idx];
        assert(s as int == sum(mapped, i as int, idx as int));
    }
    proof {
        sum_empty(mapped, j as int);
        assert(idx == j);
    }
    s
}
// </vc-code>

fn main() {}

}