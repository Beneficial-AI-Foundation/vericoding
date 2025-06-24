//Exercicio 1.a)
// ATOM 
//Exercicio 1.a)
function sum (a:array<int>, i:int, j:int) :int
reads a
requires 0 <= i <= j <= a.Length
{
    if i == j then
        0
    else
        a[j-1] + sum(a, i, j-1)
}


//Exercicio 1.b)
// SPEC 

//Exercicio 1.b)
method query (a:array<int>, i:int, j:int) returns (s:int)
requires 0 <= i <= j <= a.Length
ensures s == sum(a, i, j)
{
}


//Exercicio 1.c)
// SPEC 

//Exercicio 1.b)
method query (a:array<int>, i:int, j:int) returns (s:int)
requires 0 <= i <= j <= a.Length
ensures s == sum(a, i, j)
{
}
Lemma

// SPEC 

//Exercicio 1.b)
method query (a:array<int>, i:int, j:int) returns (s:int)
requires 0 <= i <= j <= a.Length
ensures s == sum(a, i, j)
{
}
Fast

//ATOM_PLACEHOLDER_is_prefix_sum_for

///Exercicio 2.
//ATOM_PLACEHOLDER_List//ATOM_PLACEHOLDER_from_array

//ATOM_PLACEHOLDER_mem



