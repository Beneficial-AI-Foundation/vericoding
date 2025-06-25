//ATOM




//(a)

function sum(a: array<int>, i: int, j: int): int
  reads a
  requires 0 <= i <= j <= a.Length
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
  
  /* code modified by LLM (iteration 4): added proper lemma call to establish the proof */
  sum_equals_prefix_diff(a, c, i, j);
}

/* code modified by LLM (iteration 4): completely rewrote the lemma with correct inductive proof */
lemma sum_equals_prefix_diff(a: array<int>, c: array<int>, i: int, j: int)
  requires a.Length + 1 == c.Length && c[0] == 0
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a, c)
  ensures c[j] - c[i] == sum(a, i, j)
{
  if i == j {
    // Base case: sum(a, i, i) == 0 and c[i] - c[i] == 0
  } else {
    // Inductive case: use recursion on the structure of sum
    assert i < j;
    assert i < a.Length; // since i < j <= a.Length
    
    // From is_prefix_sum_for, we know c[i+1] == c[i] + a[i]
    assert c[i+1] == c[i] + a[i];
    
    // Recursively prove for the tail
    sum_equals_prefix_diff(a, c, i+1, j);
    
    // Now we can establish the equality
    calc {
      sum(a, i, j);
    ==  // by definition of sum
      a[i] + sum(a, i+1, j);
    ==  { sum_equals_prefix_diff(a, c, i+1, j); }
      a[i] + (c[j] - c[i+1]);
    ==  // arithmetic
      a[i] + c[j] - c[i+1];
    ==  { assert c[i+1] == c[i] + a[i]; }
      a[i] + c[j] - (c[i] + a[i]);
    ==  // arithmetic
      a[i] + c[j] - c[i] - a[i];
    ==  // arithmetic
      c[j] - c[i];
    }
  }
}