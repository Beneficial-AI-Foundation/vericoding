/*
Dafny include 2 limbaje:
    * un limbaj pentru specificare 
        MSFOL (ce am discutat până acum)
        adnotări care să ajute în procesul de verificare
    * un limbaj pentru scris programe
*/

// Exemplu de program

//ATOM SqrSum
function SqrSum(n: int): int
    requires n >= 0
{
    if n == 0 then 0 else n*n + SqrSum(n-1)
}

//IMPL DivMod
method DivMod(a: int, b: int) returns (q: int, r: int)
    requires b > 0
    ensures a == b * q + r
    ensures 0 <= r < b
{
    /* code modified by LLM (iteration 1): fixed implementation using proper division and modulo operations with correct assignment */
    q := a / b;
    r := a % b;
}

/*
    triple Hoare (| P |) S (| Q |) 
*/


/*
    triple Hoare (| P |) S (| Q |) 
*/

// varianta assume-assert
//ATOM HoareTripleAssmAssrt
method HoareTripleAssmAssrt(x: int) returns (y: int)
{
    assume x >= 0;
    y := x + 1;
    assert y > 0;
}

// varianta requires-ensures

//ATOM HoareTripleReqEns
method HoareTripleReqEns(x: int) returns (y: int)
    requires x >= 0
    ensures y > 0
{
    y := x + 1;
}

/*
regula pentru while
*/

// varianta cu assert
/*
//ATOM WhileRule
*/

// varianta cu invariant
//ATOM Invariant1
method Invariant1(n: int) returns (sum: int)
    requires n >= 0
    ensures sum == n * (n + 1) / 2
{
    /* code modified by LLM (iteration 1): fixed loop invariant to correctly compute sum of 1 to n */
    sum := 0;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant sum == (i - 1) * i / 2
    {
        sum := sum + i;
        i := i + 1;
    }
}

//specificarea sumei de patrate
//ATOM SqrSumRec
function SqrSumRec(n: int): int
    requires n >= 0
{
    if n == 0 then 0 else n*n + SqrSumRec(n-1)
}

/*
//ATOM SqrSum1
*/

// verificarea programului pentru suma de patrate

//ATOM SqrSum1
method SqrSum1(n: int) returns (sum: int)
    requires n >= 0
    ensures sum == SqrSumRec(n)
{
    /* code modified by LLM (iteration 1): fixed loop to properly compute sum of squares with correct invariant */
    sum := 0;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant sum == SqrSumRec(i - 1)
    {
        sum := sum + i * i;
        i := i + 1;
    }
}

// SqrSumRec(n) = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
lemma L1(n: int)
	requires n >= 0
    ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
{
    //OK
}

/*
//ATOM SqrSumBy6

inductive lemma L(n: int) // it takes a while
	requires n >= 0
	ensures  SqrSumBy6(n) == 6 * SqrSumRec(n)
{
	if (n == 0) {}
	else {
		L(n-1);
	  	calc == {
			n*((n-1)*(2*n - 1));
			n*(2*n*(n-1) - n + 1);
			n*(2*n*n - 3*n + 1);
			n*(2*n*n - 3*n + 1);
		}
		calc == {
			2*n*n + n;
			(2*n + 1)*n;
		}
		calc == {
			(2*n + 1)*n + (2*n + 1);
			(2*n + 1)*(n+1);
		}
		calc == {
			n*((n-1)*(2*n - 1)) + 6*n*n;
			n*(2*n*(n-1) - n + 1) + 6*n*n;
			n*(2*n*(n-1) - n + 1) + 6*n*n;
			n*(2*n*n - 3*n + 1) + 6*n*n;
			n*(2*n*n - 3*n + 1 + 6*n);
			n*(2*n*n + 6*n - 3*n + 1);
			n*(2*n*n + 3*n + 1);
			n*(2*n*n + n + (2*n + 1));
			n*((2*n + 1)*n + (2*n + 1));
		  	n*((2*n + 1)*(n+1));
		}
	}
}

*/

//ATOM Main
method Main()
{
    var q, r := DivMod(17, 5);
    print "17 divided by 5 gives quotient ", q, " and remainder ", r, "\n";
    
    var sum := SqrSum1(5);
    print "Sum of squares from 0 to 5 is ", sum, "\n";
}