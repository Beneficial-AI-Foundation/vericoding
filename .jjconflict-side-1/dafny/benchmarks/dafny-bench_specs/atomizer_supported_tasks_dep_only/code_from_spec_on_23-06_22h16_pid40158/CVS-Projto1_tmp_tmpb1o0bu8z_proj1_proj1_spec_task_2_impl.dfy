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
//ATOM query
method query (a:array<int>, i:int, j:int) returns (r:int)
requires 0 <= i <= j <= a.Length
ensures r == sum(a, i, j)
{
    r := sum(a, i, j);
}

//Exercicio 1.c)
// ATOM 

//Exercicio 1.c)
lemma queryLemma(a:array<int>, i:int, j:int, k:int)
    requires 0 <= i <= k <= j <= a.Length
    ensures  sum(a,i,k) + sum(a,k,j) == sum(a,i,j)
{
}


//IMPL queryFast

method queryFast (a:array<int>, c:array<int>, i:int, j:int) returns (r:int)
requires is_prefix_sum_for(a,c) && 0 <= i <= j <= a.Length < c.Length
ensures r == sum(a, i,j)
{
    /* code modified by LLM (iteration 1): Fixed the lemma call to use correct parameters (0, i, j) where i is the middle parameter, establishing that sum(a,0,i) + sum(a,i,j) == sum(a,0,j), which allows us to derive sum(a,i,j) = c[j] - c[i] */
    queryLemma(a, 0, j, i);
    r := c[j] - c[i];
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
//ATOM List
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

//ATOM from_array
function from_array<T>(a: array<T>, i: int): List<T>
reads a
requires 0 <= i <= a.Length
{
    if i == a.Length then Nil
    else Cons(a[i], from_array(a, i+1))
}

//ATOM mem
predicate mem<T>(x: T, xs: List<T>)
{
    match xs
    case Nil => false
    case Cons(y, ys) => x == y || mem(x, ys)
}