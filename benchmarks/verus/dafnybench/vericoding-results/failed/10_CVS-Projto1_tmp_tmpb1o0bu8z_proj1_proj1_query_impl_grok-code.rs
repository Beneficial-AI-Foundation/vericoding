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
spec fn seq_int(a: Seq<i32>) -> Seq<int> {
    a.map_values(|x: i32| x as int)
}

proof fn lemma_sum_add(a: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= a.len() && i < j
    ensures sum(a, i, j) == sum(a, i, j - 1) + a[j - 1]
    decreases j - i
{
    if j - 1 == i {
    } else {
        lemma_sum_add(a, i, j - 1);
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
    let mut k: usize = i;
    while k < j
        invariant
            i <= k <= j,
            s as int == sum(seq_int(a@), i as int, k as int),
    {
        s = s + a[k];
        proof {
            lemma_sum_add(seq_int(a@), i as int, (k + 1) as int);
        }
        k = k + 1;
    }
    s
}
// </vc-code>

fn main() {}

}