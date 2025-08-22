//ATOM

//specificarea sumei de patrate
function SqrSumRec(n: int) : int
	requires n >= 0
{
	if (n == 0) then 0 else n*n + SqrSumRec(n-1)
}

//IMPL SqrSum1

// verificarea programului pentru suma de patrate

method SqrSum1(n: int) returns (s: int)
	requires n >= 0
	ensures s == SqrSumRec(n)
{
	s := 0;
	var i := 0;
	/* code modified by LLM (iteration 3): Fixed loop bounds and invariant to correctly compute sum from 1 to n */
	while i < n
		invariant 0 <= i <= n
		invariant s == SqrSumRec(i)
	{
		/* code modified by LLM (iteration 3): Update i first, then add i*i to maintain correct sum */
		i := i + 1;
		s := s + i * i;
	}
}

//IMPL L1

// SqrSumRec(n) = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
/* code modified by LLM (iteration 3): Complete algebraic proof with proper arithmetic verification */
lemma L1(n: int)
	requires n >= 0
	ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
{
	if n == 0 {
		// Base case: SqrSumRec(0) = 0 and 0*(0+1)*(2*0+1)/6 = 0
		assert SqrSumRec(0) == 0;
		assert 0*(0+1)*(2*0+1)/6 == 0;
	} else {
		// Inductive step
		L1(n-1);
		// We have: SqrSumRec(n-1) == (n-1)*n*(2*(n-1)+1)/6
		// We need: SqrSumRec(n) = n*n + SqrSumRec(n-1) == n*(n+1)*(2*n+1)/6
		
		/* code modified by LLM (iteration 3): Step-by-step algebraic verification */
		var prev_sum := (n-1)*n*(2*(n-1)+1)/6;
		var target := n*(n+1)*(2*n+1)/6;
		
		// Expand the expressions for verification
		assert 2*(n-1)+1 == 2*n-1;
		assert prev_sum == (n-1)*n*(2*n-1)/6;
		
		// Show that n*n + prev_sum == target
		calc {
			n*n + prev_sum;
		==
			n*n + (n-1)*n*(2*n-1)/6;
		==
			(6*n*n + (n-1)*n*(2*n-1))/6;
		==
			(6*n*n + n*(n-1)*(2*n-1))/6;
		==
			(n*(6*n + (n-1)*(2*n-1)))/6;
		==
			(n*(6*n + (n-1)*(2*n-1)))/6;
		==  { assert 6*n + (n-1)*(2*n-1) == 6*n + 2*n*n - 3*n + 1 == 2*n*n + 3*n + 1 == (n+1)*(2*n+1); }
			(n*(n+1)*(2*n+1))/6;
		==
			target;
		}
	}
}