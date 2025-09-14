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
lemma sum_lemma(a: array<int>, i: int, j: int, k: int)
  requires 0 <= i <= k <= j <= a.Length
  ensures sum(a, i, j) == sum(a, i, k) + sum(a, k, j)
  decreases j - k
{
  if k < j {
    sum_lemma(a, i, j-1, k);
    assert sum(a, i, j) == a[j-1] + sum(a, i, j-1);
    assert sum(a, i, j-1) == sum(a, i, k) + sum(a, k, j-1);
    assert sum(a, k, j) == a[j-1] + sum(a, k, j-1);
  }
}

lemma sum_zero(a: array<int>, i: int)
  requires 0 <= i <= a.Length
  ensures sum(a, i, i) == 0
{
}

lemma prefix_sum_property(a: array<int>, c: array<int>, j: int)
  requires is_prefix_sum_for(a, c)
  requires 0 <= j <= a.Length
  ensures c[j] == sum(a, 0, j)
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method queryFast (a:array<int>, c:array<int>, i:int, j:int) returns (r:int)
requires is_prefix_sum_for(a,c) && 0 <= i <= j <= a.Length < c.Length
ensures r == sum(a, i,j)
// </vc-spec>
// <vc-code>
{
  prefix_sum_property(a, c, i);
  prefix_sum_property(a, c, j);
  r := c[j] - c[i];
  sum_lemma(a, 0, j, i);
  assert sum(a, 0, j) == sum(a, 0, i) + sum(a, i, j);
  assert r == sum(a, i, j);
}
// </vc-code>

