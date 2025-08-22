//ATOM

ghost function f2(n: nat): nat {
  if n == 0 then 0
  else 5*f2(n/3) + n%4
}


//IMPL mod2

method mod2(n:nat) returns (a:nat) 
ensures a == f2(n)
{
  /* code modified by LLM (iteration 2): call helper method for all cases */
  a := mod2Helper(n);
}

/* code modified by LLM (iteration 2): removed precondition n > 0 to handle base case properly */
method mod2Helper(n: nat) returns (result: nat)
  ensures result == f2(n)
  decreases n
{
  if n == 0 {
    result := 0;
  } else {
    var subResult := mod2Helper(n / 3);
    result := 5 * subResult + n % 4;
  }
}