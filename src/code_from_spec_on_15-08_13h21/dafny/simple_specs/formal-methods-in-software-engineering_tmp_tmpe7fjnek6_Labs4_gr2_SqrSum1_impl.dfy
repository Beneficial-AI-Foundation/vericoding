//ATOM

//specificarea sumei de patrate
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
	while i <= n
		invariant 0 <= i <= n + 1
		/* code modified by LLM (iteration 2): Fixed invariant to handle i=0 case and track that s equals sum of squares from 1 to i-1, with special case for i=0 */
		invariant i == 0 ==> s == 0
		invariant i > 0 ==> s == SqrSumRec(i-1)
	{
		/* code modified by LLM (iteration 2): Updated loop body to increment i first, then update s with i*i to maintain invariant */
		i := i + 1;
		s := s + i * i;
	}
}

//IMPL L1

least lemma L1(n: int)
	requires n >= 0
	ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
{
	if n == 0 {
		/* code modified by LLM (iteration 1): Added explicit calculation for base case */
		calc {
			SqrSumRec(0);
			== 0;
			== 0*1*1/6;
		}
	} else {
		/* code modified by LLM (iteration 1): Added inductive step with detailed calculation */
		L1(n-1);
		calc {
			SqrSumRec(n);
			== n*n + SqrSumRec(n-1);
			== { L1(n-1); }
			n*n + (n-1)*n*(2*(n-1)+1)/6;
			== n*n + (n-1)*n*(2*n-1)/6;
			== (6*n*n + (n-1)*n*(2*n-1))/6;
			== (n*(6*n + (n-1)*(2*n-1)))/6;
			== (n*(6*n + 2*n*n - 3*n + 1))/6;
			== (n*(2*n*n + 3*n + 1))/6;
			== (n*(n+1)*(2*n+1))/6;
		}
	}
}