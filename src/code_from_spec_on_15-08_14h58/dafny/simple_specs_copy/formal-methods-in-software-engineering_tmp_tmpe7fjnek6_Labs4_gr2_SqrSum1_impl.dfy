function SqrSumRec(n: int) : int
	requires n >= 0
{
	if (n == 0) then 0 else n*n + SqrSumRec(n-1)
}

//IMPL verificarea programului pentru suma de patrate

method SqrSum1(n: int) returns (s: int)
	requires n >= 0
	ensures s == SqrSumRec(n)
{
	s := 0;
	var i := 0;
	/* code modified by LLM (iteration 1): fixed loop condition and invariant to match SqrSumRec definition */
	while i < n
		invariant 0 <= i <= n
		invariant s == SqrSumRec(i)
	{
		i := i + 1;
		s := s + i * i;
	}
}

//IMPL SqrSumRec(n) = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
least lemma L1(n: int)
	requires n >= 0
	ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
{
	if n == 0 {
		// Base case: SqrSumRec(0) = 0 = 0*1*1/6
	} else {
		// Inductive step
		L1(n-1);
		// SqrSumRec(n) = n*n + SqrSumRec(n-1)
		// By IH: SqrSumRec(n-1) = (n-1)*n*(2*(n-1)+1)/6 = (n-1)*n*(2*n-1)/6
		// So: SqrSumRec(n) = n*n + (n-1)*n*(2*n-1)/6
		//                  = n * (n + (n-1)*(2*n-1)/6)
		//                  = n * (6*n + (n-1)*(2*n-1))/6
		//                  = n * (6*n + 2*n^2 - 3*n + 1)/6
		//                  = n * (2*n^2 + 3*n + 1)/6
		//                  = n * (n+1) * (2*n+1)/6
	}
}