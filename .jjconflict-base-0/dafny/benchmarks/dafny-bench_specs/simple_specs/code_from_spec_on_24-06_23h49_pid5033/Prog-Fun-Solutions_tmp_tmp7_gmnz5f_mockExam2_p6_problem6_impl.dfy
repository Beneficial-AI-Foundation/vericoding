//ATOM
// problem 6:
// name:   Gabriele Berardi
// s-number: s4878728
// table:   XXXXX

ghost function f(n: int): int {
 if n <= 0 then 1 else n + f(n-1)*f(n-2)
}


//ATOM

ghost function fSum(n: nat): int {
 // give the body of this function
 // it should return Sum(i: 0<=i < n: f(i))
 if n <= 0 then 0 else f(n-1) + fSum(n-1)
}


//IMPL problem6

/* code modified by LLM (iteration 1): Added non-ghost helper function to compute f values and iterative method to compute fSum */
function fCompiled(n: int): int {
 if n <= 0 then 1 else n + fCompiled(n-1)*fCompiled(n-2)
}

/* code modified by LLM (iteration 1): Added lemma to prove equivalence between ghost and non-ghost versions */
lemma fEquivalence(n: int)
ensures f(n) == fCompiled(n)
{
 if n <= 0 {
  // Base case
 } else {
  fEquivalence(n-1);
  fEquivalence(n-2);
 }
}

method problem6(n:nat) returns (a: int)
ensures a == fSum(n)
{
    /* code modified by LLM (iteration 1): Implemented iterative computation using non-ghost functions */
    a := 0;
    var i := 0;
    while i < n 
    invariant 0 <= i <= n
    invariant a == fSum(i)
    {
        fEquivalence(i);
        assert f(i) == fCompiled(i);
        a := a + fCompiled(i);
        i := i + 1;
    }
}