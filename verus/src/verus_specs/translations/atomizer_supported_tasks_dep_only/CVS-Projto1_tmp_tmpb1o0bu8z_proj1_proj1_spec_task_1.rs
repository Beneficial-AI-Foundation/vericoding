use vstd::prelude::*;

verus! {

//Exercicio 1.a)
// ATOM 
//Exercicio 1.a)
spec fn sum(a: &[int], i: int, j: int) -> int
    requires 0 <= i <= j <= a.len()
    decreases j - i
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
    requires 0 <= i <= j <= a.len()
    ensures s == sum(a, i, j)
{
}

//Exercicio 1.c)
// SPEC 

//Exercicio 1.b)
pub fn query(a: &[int], i: int, j: int) -> (s: int)
    requires 0 <= i <= j <= a.len()
    ensures s == sum(a, i, j)
{
}

// SPEC 

//Exercicio 1.b)
pub fn query(a: &[int], i: int, j: int) -> (s: int)
    requires 0 <= i <= j <= a.len()
    ensures s == sum(a, i, j)
{
}

//ATOM_PLACEHOLDER_is_prefix_sum_for

///Exercicio 2.
//ATOM_PLACEHOLDER_List//ATOM_PLACEHOLDER_from_array

//ATOM_PLACEHOLDER_mem

}