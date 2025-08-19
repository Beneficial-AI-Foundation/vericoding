datatype List<T> = Nil | Cons(head: T, tail: List<T>)


//ATOM
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


//ATOM

predicate is_prefix_sum_for (a:array<int>, c:array<int>)
reads c, a
{
  a.Length + 1 == c.Length
  && c[0] == 0
  && forall j :: 1 <= j <= a.Length ==> c[j] == sum(a,0,j)
}

/* code modified by LLM (iteration 1): Added helper lemma to prove the relationship between range sums and prefix sums */
lemma sum_decomposition(a: array<int>, i: int, j: int)
  requires 0 <= i <= j <= a.Length
  ensures sum(a, i, j) == sum(a, 0, j) - sum(a, 0, i)
{
  if i == j {
    assert sum(a, i, j) == 0;
    assert sum(a, 0, j) - sum(a, 0, i) == sum(a, 0, i) - sum(a, 0, i) == 0;
  } else {
    sum_decomposition(a, i, j-1);
    assert sum(a, i, j) == a[j-1] + sum(a, i, j-1);
    assert sum(a, i, j-1) == sum(a, 0, j-1) - sum(a, 0, i);
    assert sum(a, 0, j) == a[j-1] + sum(a, 0, j-1);
    assert sum(a, i, j) == a[j-1] + (sum(a, 0, j-1) - sum(a, 0, i));
    assert sum(a, i, j) == (a[j-1] + sum(a, 0, j-1)) - sum(a, 0, i);
    assert sum(a, i, j) == sum(a, 0, j) - sum(a, 0, i);
  }
}

//IMPL 

method queryFast (a:array<int>, c:array<int>, i:int, j:int) returns (r:int)
requires is_prefix_sum_for(a,c) && 0 <= i <= j <= a.Length < c.Length
ensures r == sum(a, i,j)
{
  r := c[j] - c[i];
  
  /* code modified by LLM (iteration 1): Called helper lemma and used properties from precondition to prove the postcondition */
  sum_decomposition(a, i, j);
  assert sum(a, i, j) == sum(a, 0, j) - sum(a, 0, i);
  assert sum(a, 0, j) == c[j];
  assert sum(a, 0, i) == c[i];
  assert r == c[j] - c[i] == sum(a, 0, j) - sum(a, 0, i) == sum(a, i, j);
}