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
lemma sum_split(a: array<int>, i: int, j: int)
    requires 0 <= i <= j <= a.Length
    ensures sum(a, 0, j) == sum(a, 0, i) + sum(a, i, j)
    decreases j - i
{
    if i == j {
        // Base case: sum(a, i, i) == 0
    } else {
        // Inductive case
        calc {
            sum(a, 0, j);
            == a[j-1] + sum(a, 0, j-1);
            == { if i < j-1 { sum_split(a, i, j-1); } }
               a[j-1] + sum(a, 0, i) + sum(a, i, j-1);
            == sum(a, 0, i) + (a[j-1] + sum(a, i, j-1));
            == sum(a, 0, i) + sum(a, i, j);
        }
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
    sum_split(a, i, j);
    r := c[j] - c[i];
}
// </vc-code>

