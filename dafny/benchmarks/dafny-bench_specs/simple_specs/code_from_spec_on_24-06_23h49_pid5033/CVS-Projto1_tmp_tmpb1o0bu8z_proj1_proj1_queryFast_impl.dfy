//ATOM
///Exercicio 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

//ATOM
//Exercicio 1.a)
function sum (a:array<int>, i:int, j:int) :int
reads a
requires 0 <= i <= j <= a.Length
decreases j - i
{
  if i == j then
    0
  else
    a[j-1] + sum(a, i, j-1)
}

//ATOM
predicate is_prefix_sum_for (a:array<int>, c:array<int>)
reads c, a
{
  a.Length + 1 == c.Length
  && c[0] == 0
  && forall j :: 1 <= j <= a.Length ==> c[j] == sum(a,0,j)
}

/* code modified by LLM (iteration 1): Added helper lemma to prove sum decomposition property */
lemma SumDecomposition(a: array<int>, i: int, j: int)
  reads a
  requires 0 <= i <= j <= a.Length
  decreases j - i
  ensures sum(a, 0, j) - sum(a, 0, i) == sum(a, i, j)
{
  if i == j {
    // Base case: sum(a, i, i) == 0
    assert sum(a, i, j) == 0;
    assert sum(a, 0, i) == sum(a, 0, j);
  } else {
    // Inductive case
    SumDecomposition(a, i, j-1);
    assert sum(a, 0, j-1) - sum(a, 0, i) == sum(a, i, j-1);
    assert sum(a, 0, j) == sum(a, 0, j-1) + a[j-1];
    assert sum(a, i, j) == sum(a, i, j-1) + a[j-1];
  }
}

//IMPL queryFast
method queryFast (a:array<int>, c:array<int>, i:int, j:int) returns (r:int)
/* code modified by LLM (iteration 1): Fixed precondition to remove redundant constraint */
requires is_prefix_sum_for(a,c) && 0 <= i <= j <= a.Length
ensures r == sum(a, i,j)
{
  /* code modified by LLM (iteration 1): Added lemma call to help verification */
  SumDecomposition(a, i, j);
  r := c[j] - c[i];
}