// ATOM 
function fib(n: nat): nat
{
	if n == 0 then 0 else
	if n == 1 then 1 else
		fib(n - 1) + fib(n - 2)
}

//IMPL 
method ComputeFib(n: nat) returns (b: nat)
	ensures b == fib(n)
{
	if n == 0 {
		b := 0;
	} else if n == 1 {
		b := 1;
	} else {
		var a, c := 0, 1;
		var i := 2;
		while i <= n
			invariant 2 <= i <= n + 1
			invariant a == fib(i - 2)
			invariant c == fib(i - 1)
		{
			var temp := a + c;
			a := c;
			c := temp;
			i := i + 1;
		}
		b := c;
	}
}

//ATOM_PLACEHOLDER_Main