use vstd::prelude::*;

verus! {

spec fn sum(a: &[i32], i: int, j: int) -> int
    recommends 0 <= i <= j <= a.len()
{
    if i == j { 0 } else { a[j-1] + sum(a, i, j-1) }
}

pub fn query(a: &[i32], i: usize, j: usize) -> (res: i32)
    requires 0 <= i <= j <= a.len()
    ensures res == sum(a, i as int, j as int)
{
}

pub fn queryFast(a: &[i32], c: &[i32], i: usize, j: usize) -> (r: i32)
    requires 0 <= i <= j <= a.len()
    requires is_prefix_sum_for(a, c)
    ensures r == sum(a, i as int, j as int)
{
}

spec fn is_prefix_sum_for(a: &[i32], c: &[i32]) -> bool
{
    a.len() + 1 == c.len() && forall|i: int| 0 <= i <= a.len() ==> c[i] == sum(a, 0, i)
}

proof fn proof(a: &[i32], i: int, j: int, k: int)
    requires 0 <= i <= k <= j <= a.len()
    ensures sum(a, i, k) + sum(a, k, j) == sum(a, i, j)
{
}

enum List<T> {
    Nil,
    Cons { head: T, tail: Box<List<T>> }
}

pub fn from_array<T>(a: &[T]) -> (l: List<T>)
    ensures forall|i: int| 0 <= i < a.len() ==> mem(a[i], l)
    ensures forall|x: T| mem(x, l) ==> exists|y: int| 0 <= y < a.len() && a[y] == x
{
}

spec fn mem<T>(x: T, l: List<T>) -> bool
{
    match l {
        List::Nil => false,
        List::Cons { head: h, tail: t } => h == x || mem(x, *t)
    }
}

}