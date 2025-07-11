//ATOM
function fib(n: nat): nat
{
	if n == 0 then 0 else
	if n == 1 then 1 else
		fib(n - 1) + fib(n - 2)
}


//ATOM
method ComputeFib(n: nat) returns (b: nat)
	ensures b == fib(n)
{
  b := 0;
  assume b == fib(n);
  return b;
}


//IMPL Main
method Main()
{
	/* code modified by LLM (iteration 1): fixed method call to properly handle return value */
	var ret := ComputeFib(5);
}