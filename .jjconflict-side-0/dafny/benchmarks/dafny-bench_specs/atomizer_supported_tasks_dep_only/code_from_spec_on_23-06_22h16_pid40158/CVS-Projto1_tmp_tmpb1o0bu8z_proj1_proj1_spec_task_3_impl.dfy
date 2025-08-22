//Exercicio 1.a)
//ATOM_PLACEHOLDER_sum

//Exercicio 1.b)
//ATOM_PLACEHOLDER_query

//Exercicio 1.c)
//ATOM_PLACEHOLDER_queryLemma

//ATOM_PLACEHOLDER_queryFast

//ATOM_PLACEHOLDER_is_prefix_sum_for

///Exercicio 2.
//ATOM_PLACEHOLDER_List

//IMPL 
method from_array<T>(a: array<T>) returns (l: List<T>)
requires a.Length > 0
ensures forall j::0 <= j < a.Length ==> mem(a[j],l)
{
    l := Nil;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> mem(a[k], l)
    {
        l := Cons(a[i], l);
        i := i + 1;
    }
}

// ATOM 
function mem<T(==)> (x: T, l:List<T>) : bool
{
    match l
    case Nil => false
    case Cons(y,r)=> if (x==y) then true else mem(x,r)
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)