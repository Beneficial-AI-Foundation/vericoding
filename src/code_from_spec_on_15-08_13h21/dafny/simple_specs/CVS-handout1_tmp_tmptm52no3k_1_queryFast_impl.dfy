/* code modified by LLM (iteration 1): added decreases clause to prove termination */
function sum(a: array<int>, i: int, j: int): int
  reads a
  requires 0 <= i <= j <= a.Length
  decreases j - i
{
  if (i == j) then 0
  else a[i] + sum(a, i+1, j)
}

//ATOM

//(c)

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
  requires a.Length + 1 == c.Length
  requires c[0] == 0
  reads c, a
{
  forall i: int :: 0 <= i < a.Length ==> c[i+1] == c[i] + a[i]
}

//IMPL 

method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
  requires a.Length + 1 == c.Length && c[0] == 0
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a,c) 
  ensures r == sum(a, i, j)
{
  r := c[j] - c[i];
  
  // Help Dafny verify the correctness with a lemma call
  prefix_sum_correctness_lemma(a, c, i, j);
}

/* code modified by LLM (iteration 1): added decreases clause to prove termination */
lemma prefix_sum_correctness_lemma(a: array<int>, c: array<int>, i: int, j: int)
  requires a.Length + 1 == c.Length && c[0] == 0
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a, c)
  ensures c[j] - c[i] == sum(a, i, j)
  decreases j - i
{
  if i == j {
    // Base case: sum(a, i, i) == 0 and c[i] - c[i] == 0
  } else {
    // Inductive case
    prefix_sum_correctness_lemma(a, c, i+1, j);
    // c[j] - c[i] == (c[j] - c[i+1]) + (c[i+1] - c[i])
    //              == sum(a, i+1, j) + a[i]  (by IH and prefix sum property)
    //              == a[i] + sum(a, i+1, j)
    //              == sum(a, i, j)  (by definition of sum)
  }
}