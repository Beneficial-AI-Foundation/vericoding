//ATOM

//specificarea sumei de patrate
function SqrSumRec(n: int) : int
	requires n >= 0
{
	if (n == 0) then 0 else n*n + SqrSumRec(n-1)
}
/*


// SPEC

// verificarea programului pentru suma de patrate

method SqrSum1(n: int) returns (s: int)
	requires n >= 0
	ensures s == SqrSumRec(n)
{
}

// SqrSumRec(n) = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
least lemma L1(n: int)
	requires n >= 0
  ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
{
}

/*
