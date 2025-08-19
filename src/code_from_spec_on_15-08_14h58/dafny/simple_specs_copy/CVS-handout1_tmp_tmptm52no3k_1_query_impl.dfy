//ATOM
function sum(a: array<int>, i: int, j: int): int
  reads a
  requires 0 <= i <= j <= a.Length
  /* code modified by LLM (iteration 1): added decreases clause to prove termination */
  decreases j - i
{
  if (i == j) then 0
  else a[i] + sum(a, i+1, j)
}

//IMPL query

/* code modified by LLM (iteration 4): added helper lemma to prove sum extension property */
lemma SumExtension(a: array<int>, i: int, j: int)
  reads a
  requires 0 <= i <= j < a.Length
  ensures sum(a, i, j+1) == sum(a, i, j) + a[j]
  decreases j - i
{
  if i == j {
    assert sum(a, i, j) == 0;
    assert sum(a, i, j+1) == a[i] + sum(a, i+1, j+1);
    assert sum(a, i+1, j+1) == 0;
  } else {
    SumExtension(a, i+1, j);
    assert sum(a, i, j+1) == a[i] + sum(a, i+1, j+1);
    assert sum(a, i+1, j+1) == sum(a, i+1, j) + a[j];
    assert sum(a, i, j) == a[i] + sum(a, i+1, j);
  }
}

method query(a: array<int>, i: int, j: int) returns (res:int)
  requires 0 <= i <= j <= a.Length
  ensures res == sum(a, i, j)
{
  res := 0;
  var k := i;
  
  while k < j
    invariant i <= k <= j
    invariant res == sum(a, i, k)
  {
    /* code modified by LLM (iteration 4): use helper lemma to prove sum extension */
    SumExtension(a, i, k);
    assert sum(a, i, k+1) == sum(a, i, k) + a[k];
    res := res + a[k];
    k := k + 1;
  }
}