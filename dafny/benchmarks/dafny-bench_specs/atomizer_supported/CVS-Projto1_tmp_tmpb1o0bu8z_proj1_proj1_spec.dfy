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
// ATOM 

//Exercicio 1.c)
lemma queryLemma(a:array<int>, i:int, j:int, k:int)
    requires 0 <= i <= k <= j <= a.Length
    ensures  sum(a,i,k) + sum(a,k,j) == sum(a,i,j)
{
}


// SPEC 

method queryFast (a:array<int>, c:array<int>, i:int, j:int) returns (r:int)
requires is_prefix_sum_for(a,c) && 0 <= i <= j <= a.Length < c.Length
ensures r == sum(a, i,j)
{
}


// ATOM 

predicate is_prefix_sum_for (a:array<int>, c:array<int>)
reads c, a
{
    a.Length + 1 == c.Length
    && c[0] == 0
    && forall j :: 1 <= j <= a.Length ==> c[j] == sum(a,0,j)
}


///Exercicio 2.
// ATOM 

///Exercicio 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)
// SPEC 

method from_array<T>(a: array<T>) returns (l: List<T>)
requires a.Length > 0
ensures forall j::0 <= j < a.Length ==> mem(a[j],l)
{
}


// ATOM 

function mem<T(==)> (x: T, l:List<T>) : bool
{
    match l
    case Nil => false
    case Cons(y,r)=> if (x==y) then true else mem(x,r)
}




