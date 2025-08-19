//ATOM

//specificarea sumei de patrate
function SqrSumRec(n: int) : int
	requires n >= 0
{
	if (n == 0) then 0 else n*n + SqrSumRec(n-1)
}

//IMPL SqrSum1
method SqrSum1(n: int) returns (s: int)
	requires n >= 0
	ensures s == SqrSumRec(n)
{
	s := 0;
	var i := 0;
	/* code modified by LLM (iteration 1): Fixed loop condition from i <= n to i < n, and corrected loop invariant syntax */
	while i < n
		invariant 0 <= i <= n
		invariant s == SqrSumRec(i)
	{
		/* code modified by LLM (iteration 1): Increment i first, then add i*i to maintain invariant */
		i := i + 1;
		s := s + i * i;
	}
}

//IMPL L1
/* code modified by LLM (iteration 1): Changed 'least lemma' to 'lemma' to fix compilation error */
lemma L1(n: int)
	requires n >= 0
	ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
{
	if n == 0 {
		// Base case: SqrSumRec(0) = 0 and 0*1*1/6 = 0
	} else {
		// Inductive step
		L1(n-1);
		/* code modified by LLM (iteration 1): Added explicit arithmetic assertions to help Dafny verify the algebraic manipulation */
		assert SqrSumRec(n-1) == (n-1)*n*(2*(n-1)+1)/6;
		assert SqrSumRec(n) == n*n + SqrSumRec(n-1);
		assert SqrSumRec(n) == n*n + (n-1)*n*(2*n-1)/6;
		assert 6*n*n + (n-1)*n*(2*n-1) == n*(6*n + (n-1)*(2*n-1));
		assert 6*n + (n-1)*(2*n-1) == 6*n + 2*n*n - 3*n + 1;
		assert 6*n + 2*n*n - 3*n + 1 == 2*n*n + 3*n + 1;
		assert 2*n*n + 3*n + 1 == (n+1)*(2*n+1);
	}
}