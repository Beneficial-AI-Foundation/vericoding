//ATOM f
// problem 6:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXXXX

ghost function f(n: int): int {
  if n <= 0 then 1 else n + f(n-1)*f(n-2)
}

//ATOM fSum
ghost function fSum(n: nat): int {
 // give the body of this function
  // it should return Sum(i: 0<=i < n: f(i))
  if n <= 0 then 0 else f(n-1) + fSum(n-1)
}

/* code modified by LLM (iteration 1): added helper lemma to prove fSum property */
lemma fSumProperty(i: nat)
  ensures fSum(i+1) == f(i) + fSum(i)
{
  // The proof follows directly from the definition of fSum
}

//IMPL problem6
method problem6(n:nat) returns (a: int)
ensures a == fSum(n)
{
  a := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a == fSum(i)
  {
    /* code modified by LLM (iteration 1): simplified loop body with lemma call */
    fSumProperty(i);
    a := a + f(i);
    i := i + 1;
  }
}