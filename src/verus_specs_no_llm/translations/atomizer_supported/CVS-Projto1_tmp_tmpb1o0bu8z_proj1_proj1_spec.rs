// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_prefix_sum_for(a: Vec<int>, c: Vec<int>, a
{
    a.Length + 1 == c.Length
    && c[0] == 0
    && forall j: : 1 <= j <= a.Length ==> c[j] == sum(a, 0, j)
}


///Exercicio 2.
// ATOM 

///Exercicio 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)
// SPEC 

method from_array<T>(a: array<T>) returns (l: List<T>)
requires a.Length > 0
ensures forall j::0 <= j < a.Length ==> mem(a[j], l) -> bool {
    
}

fn query(a: Vec<int>, i: int, j: int) -> (s: int)
    requires
        0 <= i <= j <= a.len()
    ensures
        s == sum(a, i, j)
{
    return 0;
}

}