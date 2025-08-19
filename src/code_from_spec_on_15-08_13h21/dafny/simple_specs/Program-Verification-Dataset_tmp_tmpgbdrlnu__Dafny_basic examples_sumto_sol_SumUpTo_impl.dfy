//ATOM
function sum_up_to (n: nat): nat
{
 if (n == 0) then 0
 else sum_up_to (n-1) + 1
}

//IMPL 
method SumUpTo (n: nat) returns (r: nat)
 ensures r == sum_up_to (n)
{
  /* code modified by LLM (iteration 1): added helper lemma and lemma call to prove sum_up_to(n) == n */
  sum_up_to_equals_n(n);
  r := n;
}

/* code modified by LLM (iteration 1): helper lemma to prove sum_up_to(n) == n */
lemma sum_up_to_equals_n(n: nat)
  ensures sum_up_to(n) == n
{
  if n == 0 {
    // Base case: sum_up_to(0) == 0
  } else {
    // Inductive case: sum_up_to(n) == sum_up_to(n-1) + 1 == (n-1) + 1 == n
    sum_up_to_equals_n(n-1);
  }
}