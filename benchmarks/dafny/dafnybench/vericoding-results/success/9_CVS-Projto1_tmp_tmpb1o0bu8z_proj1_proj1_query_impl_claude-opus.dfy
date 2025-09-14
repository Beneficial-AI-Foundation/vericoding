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
lemma sum_step(a: array<int>, i: int, j: int)
    requires 0 <= i < j <= a.Length
    ensures sum(a, i, j) == sum(a, i, j-1) + a[j-1]
{
    // This follows directly from the definition of sum
}

lemma sum_accumulate(a: array<int>, i: int, k: int, j: int)
    requires 0 <= i <= k <= j <= a.Length
    ensures sum(a, i, j) == sum(a, i, k) + sum(a, k, j)
    decreases j - k
{
    if k == j {
        assert sum(a, k, j) == 0;
    } else {
        sum_accumulate(a, i, k, j-1);
        assert sum(a, i, j) == sum(a, i, j-1) + a[j-1];
        assert sum(a, i, j-1) == sum(a, i, k) + sum(a, k, j-1);
        assert sum(a, k, j) == sum(a, k, j-1) + a[j-1];
    }
}
// </vc-helpers>

// <vc-spec>
method query (a:array<int>, i:int, j:int) returns (s:int)
requires 0 <= i <= j <= a.Length
ensures s == sum(a, i, j)
// </vc-spec>
// <vc-code>
{
    s := 0;
    var k := i;
    
    while k < j
        invariant i <= k <= j
        invariant s == sum(a, i, k)
    {
        s := s + a[k];
        sum_accumulate(a, i, k, k+1);
        k := k + 1;
    }
}
// </vc-code>

