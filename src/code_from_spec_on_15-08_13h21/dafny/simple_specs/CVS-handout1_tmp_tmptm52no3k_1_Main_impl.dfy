//ATOM

function sum(a: array<int>, i: int, j: int): int
  reads a
  requires 0 <= i <= j <= a.Length
  /* code modified by LLM (iteration 1): Added decreases clause to prove termination */
  decreases j - i
{
  if (i == j) then 0
  else a[i] + sum(a, i+1, j)
}

//ATOM

method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
  requires a.Length + 1 == c.Length && c[0] == 0
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a,c) 
  ensures r == sum(a, i, j)
{
  /* code modified by LLM (iteration 1): Fixed implementation to match postcondition using prefix sum property */
  r := c[j] - c[i];
  
  /* code modified by LLM (iteration 1): Added lemma call to prove correctness */
  prefix_sum_correctness_lemma(a, c, i, j);
}

//ATOM

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
  requires a.Length + 1 == c.Length
  requires c[0] == 0
  reads c, a
{
  forall i: int :: 0 <= i < a.Length ==> c[i+1] == c[i] + a[i]
}

/* code modified by LLM (iteration 1): Added helper lemma to prove prefix sum correctness */
lemma prefix_sum_correctness_lemma(a: array<int>, c: array<int>, i: int, j: int)
  requires a.Length + 1 == c.Length && c[0] == 0
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a, c)
  ensures c[j] - c[i] == sum(a, i, j)
{
  if i == j {
    assert sum(a, i, j) == 0;
    assert c[j] - c[i] == 0;
  } else {
    prefix_sum_correctness_lemma(a, c, i+1, j);
    assert c[j] - c[i+1] == sum(a, i+1, j);
    assert c[i+1] == c[i] + a[i];
    assert c[j] - c[i] == (c[j] - c[i+1]) + a[i];
    assert c[j] - c[i] == sum(a, i+1, j) + a[i];
    assert sum(a, i, j) == a[i] + sum(a, i+1, j);
  }
}

//IMPL 

method Main()
{
  var x := new int[4];
  /* code modified by LLM (iteration 1): Initialize array elements to match expected values */
  x[0], x[1], x[2], x[3] := 2, 2, 1, 5;
  var y := sum(x, 0, x.Length);
  
  /* code modified by LLM (iteration 1): Added lemma call to help prove the sum value */
  sum_calculation_lemma(x);
  assert y == 10;
  
  var c := new int[5];
  /* code modified by LLM (iteration 1): Initialize prefix sum array with correct values */
  c[0], c[1], c[2], c[3], c[4] := 0, 2, 4, 5, 10;
  
  /* code modified by LLM (iteration 1): Added assertion to verify prefix sum property */
  assert is_prefix_sum_for(x, c);
  
  var r := queryFast(x, c, 0, x.Length);
}

/* code modified by LLM (iteration 1): Added helper lemma to prove specific sum calculation */
lemma sum_calculation_lemma(x: array<int>)
  requires x.Length == 4
  requires x[0] == 2 && x[1] == 2 && x[2] == 1 && x[3] == 5
  ensures sum(x, 0, 4) == 10
{
  assert sum(x, 0, 4) == x[0] + sum(x, 1, 4);
  assert sum(x, 1, 4) == x[1] + sum(x, 2, 4);
  assert sum(x, 2, 4) == x[2] + sum(x, 3, 4);
  assert sum(x, 3, 4) == x[3] + sum(x, 4, 4);
  assert sum(x, 4, 4) == 0;
  assert sum(x, 0, 4) == 2 + 2 + 1 + 5;
}