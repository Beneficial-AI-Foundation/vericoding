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
proof fn lemma_sum_recursive_property(a: Seq<int>, i: int, j: int)
    requires 0 <= i < j <= a.len()
    ensures sum(a, i, j) == a[j - 1] + sum(a, i, j - 1)
{
}

proof fn lemma_sum_single_element(a: Seq<int>, i: int)
    requires 0 <= i < a.len()
    ensures sum(a, i, i + 1) == a[i]
{
}

proof fn lemma_sum_empty_range(a: Seq<int>, i: int)
    requires 0 <= i <= a.len()
    ensures sum(a, i, i) == 0
{
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
            s == sum(a@.map(|idx, x| x as int), i as int, k as int)
        decreases j - k
    {
        s = s + a[k];
        k = k + 1;
        
        proof {
            lemma_sum_recursive_property(a@.map(|idx, x| x as int), i as int, k as int);
        }
        
        assert(sum(a@.map(|idx, x| x as int), i as int, k as int) == 
               a@.map(|idx, x| x as int)[(k - 1) as int] + 
               sum(a@.map(|idx, x| x as int), i as int, (k - 1) as int));
    }
    
    s
}
// </vc-code>

fn main() {}

}