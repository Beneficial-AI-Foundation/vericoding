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
lemma SumProperty(a: array<int>, i: int, j: int)
  requires 0 <= i <= j <= a.Length
  ensures sum(a, i, j) == (if i == j then 0 else a[j-1] + sum(a, i, j-1))
  decreases j
{
  // This lemma is essentially restating the definition of sum, so no additional proof is needed.
}

lemma SumUpdate(a: array<int>, i: int, k: int, j: int)
  requires 0 <= i <= k <= j <= a.Length
  ensures sum(a, i, j) == sum(a, i, k) + sum(a, k, j)
  decreases j
{
  if i == j {
    assert sum(a, i, j) == 0;
    assert sum(a, i, k) == 0;
    assert sum(a, k, j) == 0;
  } else if k == j {
    assert sum(a, i, j) == sum(a, i, k);
    assert sum(a, k, j) == 0;
  } else if i == k {
    assert sum(a, i, k) == 0;
    assert sum(a, i, j) == sum(a, k, j);
  } else {
    calc {
      sum(a, i, j);
      == { SumProperty(a, i, j); }
      a[j-1] + sum(a, i, j-1);
      == { SumUpdate(a, i, k, j-1); }
      a[j-1] + sum(a, i, k) + sum(a, k, j-1);
      == { SumProperty(a, k, j); }
      sum(a, i, k) + (a[j-1] + sum(a, k, j-1));
      == { SumProperty(a, k, j); }
      sum(a, i, k) + sum(a, k, j);
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method query (a:array<int>, i:int, j:int) returns (s:int)
requires 0 <= i <= j <= a.Length
ensures s == sum(a, i, j)
// </vc-spec>
// </vc-spec>

// <vc-code>
method Query(a: array<int>, i: int, j: int) returns (s: int)
  requires 0 <= i <= j <= a.Length
  ensures s == sum(a, i, j)
{
  s := 0;
  var k := i;
  while k < j
    invariant i <= k <= j
    invariant s == sum(a, i, k)
    decreases j - k
  {
    s := s + a[k];
    k := k + 1;
    assert s == sum(a, i, k);
  }
}
// </vc-code>
