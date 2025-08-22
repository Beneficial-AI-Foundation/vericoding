//Exercicio 1.a)
function sum (a:array<int>, i:int, j:int) :int
decreases j
reads a
requires 0 <= i <= j <= a.Length
{
    if i == j then
        0
    else
        a[j-1] + sum(a, i, j-1)
}

//Exercicio 1.b)

// <vc-helpers>
// </vc-helpers>

method query (a:array<int>, i:int, j:int) returns (s:int)
requires 0 <= i <= j <= a.Length
ensures s == sum(a, i, j)
// <vc-code>
{
  assume false;
}
// </vc-code>

//Exercicio 1.c)
lemma queryLemma(a:array<int>, i:int, j:int, k:int)
    requires 0 <= i <= k <= j <= a.Length
    ensures  sum(a,i,k) + sum(a,k,j) == sum(a,i,j)
{
}


predicate is_prefix_sum_for (a:array<int>, c:array<int>)
reads c, a
{
    a.Length + 1 == c.Length
    && c[0] == 0
    && forall j :: 1 <= j <= a.Length ==> c[j] == sum(a,0,j)
}

///Exercicio 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

method from_array<T>(a: array<T>) returns (l: List<T>)
requires a.Length > 0
ensures forall j::0 <= j < a.Length ==> mem(a[j],l)
{
    var i:= a.Length-1;
    l:= Nil;

    while (i >= 0)
    invariant -1 <= i < a. Length
    invariant forall j:: i+1 <= j < a.Length ==> mem(a[j],l)
    {
        l := Cons(a[i], l);
        i := i - 1;
    }

    return l;
}

function mem<T(==)> (x: T, l:List<T>) : bool
decreases l
{
    match l
    case Nil => false
    case Cons(y,r)=> if (x==y) then true else mem(x,r)
}