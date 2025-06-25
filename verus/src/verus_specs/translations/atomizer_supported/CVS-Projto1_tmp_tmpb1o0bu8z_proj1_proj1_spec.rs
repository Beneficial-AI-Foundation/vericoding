use vstd::prelude::*;

verus! {

//Exercicio 1.a)
// ATOM 
//Exercicio 1.a)
spec fn sum(a: &[int], i: int, j: int) -> int
    recommends 0 <= i <= j <= a.len()
{
    if i == j {
        0
    } else {
        a[j-1] + sum(a, i, j-1)
    }
}

//Exercicio 1.b)
// SPEC 

//Exercicio 1.b)
pub fn query(a: &[int], i: int, j: int) -> (s: int)
    requires(0 <= i <= j <= a.len())
    ensures(s == sum(a, i, j))
{
}

//Exercicio 1.c)
// ATOM 

//Exercicio 1.c)
proof fn queryLemma(a: &[int], i: int, j: int, k: int)
    requires(0 <= i <= k <= j <= a.len())
    ensures(sum(a,i,k) + sum(a,k,j) == sum(a,i,j))
{
}

// SPEC 

pub fn queryFast(a: &[int], c: &[int], i: int, j: int) -> (r: int)
    requires(is_prefix_sum_for(a,c) && 0 <= i <= j <= a.len() < c.len())
    ensures(r == sum(a, i,j))
{
}

// ATOM 

spec fn is_prefix_sum_for(a: &[int], c: &[int]) -> bool
{
    a.len() + 1 == c.len()
    && c[0] == 0
    && forall|j: int| 1 <= j <= a.len() ==> c[j] == sum(a,0,j)
}

///Exercicio 2.
// ATOM 

///Exercicio 2.
enum List<T> {
    Nil,
    Cons { head: T, tail: Box<List<T>> }
}

// SPEC 

pub fn from_array<T>(a: &[T]) -> (l: List<T>)
    requires(a.len() > 0)
    ensures(forall|j: int| 0 <= j < a.len() ==> mem(a[j], l))
{
}

// ATOM 

spec fn mem<T>(x: T, l: List<T>) -> bool
{
    match l {
        List::Nil => false,
        List::Cons { head: y, tail: r } => if x == y { true } else { mem(x, *r) }
    }
}

}