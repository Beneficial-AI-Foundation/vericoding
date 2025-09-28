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
proof fn lemma_sum_base(a: Seq<int>, i: int)
    requires 0 <= i <= a.len()
    ensures sum(a, i, i) == 0
{
    reveal_with_fuel(sum, 1);
}

proof fn lemma_sum_step(a: Seq<int>, i: int, j: int)
    requires 0 <= i <= j < a.len()
    ensures sum(a, i, j + 1) == a[j] + sum(a, i, j)
{
    reveal_with_fuel(sum, 1);
}
// </vc-helpers>

// <vc-spec>
exec fn query(a: &[i32], i: usize, j: usize) -> (s: i32)
    requires 0 <= i <= j <= a.len()
    ensures s == sum(a@.map(|k, x| x as int), i as int, j as int)
// </vc-spec>
// <vc-code>
{
    let seq_int = a@.map(|k, x| x as int);
    let mut k: usize = i;
    let mut acc: i32 = 0;

    proof {
        assert(seq_int.len() == a.len() as int);
        assert(0 <= i as int <= j as int <= seq_int.len());
        lemma_sum_base(seq_int, i as int);
        assert(k == i);
        assert
// </vc-code>

fn main() {}

}