//ATOM
predicate Par(n:int)
{
  n % 2 == 0
}

//IMPL 
method FazAlgo (a:int, b:int) returns (x:int, y:int)
requires a >= b && Par (a-b)
/* code modified by LLM (iteration 1): added missing opening brace for method body */
{
  x := 0;
  y := 0;
}