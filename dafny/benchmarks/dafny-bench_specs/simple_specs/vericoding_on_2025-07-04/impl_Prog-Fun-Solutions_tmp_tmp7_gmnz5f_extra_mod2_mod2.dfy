//ATOM

ghost function f2(n: nat): nat {
  if n == 0 then 0
  else 5*f2(n/3) + n%4
}

//IMPL 

method mod2(n:nat) returns (a:nat) 
ensures a == f2(n)
{
  /* code modified by LLM (iteration 1): Added recursive implementation with explicit termination proof */
  a := computeF2(n);
}

/* code modified by LLM (iteration 1): Helper method to compute f2 with explicit decreasing measure */
method computeF2(n: nat) returns (result: nat)
  ensures result == f2(n)
  decreases n
{
  if n == 0 {
    result := 0;
  } else {
    var subResult := computeF2(n / 3);
    result := 5 * subResult + n % 4;
  }
}