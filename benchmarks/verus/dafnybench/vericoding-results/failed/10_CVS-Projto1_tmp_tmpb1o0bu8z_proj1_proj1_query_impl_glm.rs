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
proof fn lemma_sum_step(a: Seq<int>, i: int, k: int, total: int)
    requires 0 <= i <= k < a.len(),
    requires total == sum(a, i, k),
    ensures total + a@[k] == sum(a, i, k+1),
{
    assert(sum(a, i, k+1) == a@[k] + sum(a, i, k));
}
// </vc-helpers>

// <vc-spec>
exec fn query(a: &[i32], i: usize, j: usize) -> (s: i32)
    requires 0 <= i <= j <= a.len()
    ensures s == sum(a@.map(|k, x| x as int), i as int, j as int)
// </vc-spec>
// <vc-code>
{
    let a_seq = a@.map(|_, x| x as int);
    let mut total: int = 0;
    let mut k = i;
    while k < j
        invariant i <= k <= j
        invariant total == sum(a_seq, i as int, k as int)
    {
        proof {
            lemma_sum_step(a_seq, i as int, k as int, total);
        }
        total += a_seq[k];
        k += 1;
    }
    total as i32
}
// </vc-code>

fn main() {}

}