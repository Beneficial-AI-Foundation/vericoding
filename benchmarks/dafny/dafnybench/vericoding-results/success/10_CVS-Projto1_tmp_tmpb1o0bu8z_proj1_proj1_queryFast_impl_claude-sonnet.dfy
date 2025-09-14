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

//Exercicio 1.c)

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
  assume{:axiom} false;
}

function mem<T(==)> (x: T, l:List<T>) : bool
decreases l
{
    match l
    case Nil => false
    case Cons(y,r)=> if (x==y) then true else mem(x,r)
}

// <vc-helpers>
lemma sum_prefix_property(a: array<int>, c: array<int>, i: int, j: int)
requires is_prefix_sum_for(a, c)
requires 0 <= i <= j <= a.Length
ensures sum(a, i, j) == c[j] - c[i]
decreases j - i
{
    if i == j {
        assert sum(a, i, j) == 0;
        assert c[i] == sum(a, 0, i);
        assert c[j] == sum(a, 0, j);
        assert c[j] - c[i] == 0;
    } else {
        sum_prefix_property(a, c, i, j-1);
        assert sum(a, i, j-1) == c[j-1] - c[i];
        assert sum(a, i, j) == a[j-1] + sum(a, i, j-1);
        assert sum(a, i, j) == a[j-1] + c[j-1] - c[i];
        assert c[j] == sum(a, 0, j);
        assert c[j-1] == sum(a, 0, j-1);
        sum_split_property(a, 0, j-1, j);
        assert sum(a, 0, j) == sum(a, 0, j-1) + a[j-1];
        assert c[j] == c[j-1] + a[j-1];
        assert a[j-1] + c[j-1] - c[i] == c[j] - c[i];
    }
}

lemma sum_split_property(a: array<int>, i: int, k: int, j: int)
requires 0 <= i <= k <= j <= a.Length
ensures sum(a, i, j) == sum(a, i, k) + sum(a, k, j)
decreases j - k
{
    if k == j {
        assert sum(a, k, j) == 0;
    } else {
        sum_split_property(a, i, k, j-1);
        assert sum(a, i, j-1) == sum(a, i, k) + sum(a, k, j-1);
        assert sum(a, i, j) == a[j-1] + sum(a, i, j-1);
        assert sum(a, k, j) == a[j-1] + sum(a, k, j-1);
    }
}
// </vc-helpers>

// <vc-spec>
method queryFast (a:array<int>, c:array<int>, i:int, j:int) returns (r:int)
requires is_prefix_sum_for(a,c) && 0 <= i <= j <= a.Length < c.Length
ensures r == sum(a, i,j)
// </vc-spec>
// <vc-code>
{
    sum_prefix_property(a, c, i, j);
    r := c[j] - c[i];
}
// </vc-code>

