// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(a: Seq<int>, i: int, j: int) -> int
    decreases j - i
{
    if i == j {
        0
    } else if i < j && j-1 < a.len() {
        a[j-1] + sum(a, i, j-1)
    } else {
        0
    }
}

spec fn is_prefix_sum_for(a: Seq<int>, c: Seq<int>) -> bool {
    a.len() + 1 == c.len()
    && c[0] == 0
    && forall |j: int| #![auto] 1 <= j <= a.len() ==> c[j] == sum(a, 0, j)
}

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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn query_fast(a: Vec<i8>, c: Vec<i8>, i: i8, j: i8) -> (r: i8)
    requires 
        is_prefix_sum_for(a@.map(|_i: int, x: i8| x as int), c@.map(|_i: int, x: i8| x as int)) && 0 <= i as int <= j as int <= a.len() < c.len()
    ensures r as int == sum(a@.map(|_i: int, x: i8| x as int), i as int, j as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}