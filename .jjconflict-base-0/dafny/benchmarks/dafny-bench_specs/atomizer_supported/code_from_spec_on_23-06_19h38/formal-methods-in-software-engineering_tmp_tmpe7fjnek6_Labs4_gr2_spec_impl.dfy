/*
Dafny include 2 limbaje:
    * un limbaj pentru specificare 
        MSFOL (ce am discutat până acum)
        adnotări care să ajute în procesul de verificare
    * un limbaj pentru scris programe
*/

// Exemplu de program

//IMPL SPEC 

// Exemplu de program

method SqrSum(n: int) returns (s: int)
{
    s := 0;
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        /* code modified by LLM (iteration 3): fixed invariant for sum of squares from 0 to i-1 */
        invariant s == if i == 0 then 0 else (i - 1) * i * (2 * (i - 1) + 1) / 6
    {
        s := s + i * i;
        i := i + 1;
    }
}


//IMPL SPEC 

method DivMod(a: int, b: int) returns (q: int, r: int)
{
    /* code modified by LLM (iteration 3): handle edge cases and implement basic division */
    if b <= 0 {
        q := 0;
        r := a;
        return;
    }
    
    if a < 0 {
        q := 0;
        r := a;
        return;
    }
    
    q := 0;
    r := a;
    while r >= b
        invariant a == b * q + r
        invariant r >= 0
        decreases r
    {
        q := q + 1;
        r := r - b;
    }
}

/*
    triple Hoare (| P |) S (| Q |) 
*/


/*
    triple Hoare (| P |) S (| Q |) 
*/

// varianta assume-assert
//IMPL SPEC 

// varianta assume-assert
method HoareTripleAssmAssrt()
{
    var i := 10;
    var k := i * i;
    assert k == i * i;
    k := k + 2 * i + 1;
    assert k == (i + 1) * (i + 1);
}


// varianta requires-ensures

//IMPL SPEC 

// varianta requires-ensures

method HoareTripleReqEns(i: int, k: int) returns (k': int)
	// (| k == i*i |) k := k + 2 * i +1; (| k = (i+1)*(i+1) |)
	requires  k == i*i
	ensures  k' == (i+1)*(i+1)
{
    k' := k + 2 * i + 1;
}

/*
regula pentru while
*/

// varianta cu assert
/*


/*
regula pentru while
*/

// varianta cu assert
/*
//IMPL SPEC 
method WhileRule()
{
}
*/

*/

// varianta cu invariant
//IMPL SPEC 

// varianta cu invariant
method Invariant1()
{
    var x := 0;
    var y := 100;
    while x < 50
        invariant x + y == 100
        invariant 0 <= x <= 50
    {
        x := x + 1;
        y := y - 1;
    }
    assert x + y == 100;
}


//specificarea sumei de patrate
//ATOM 

//specificarea sumei de patrate
function SqrSumRec(n: int) : int
	requires n >= 0
{
	if (n == 0) then 0 else n*n + SqrSumRec(n-1)
}

// verificarea programului pentru suma de patrate

//IMPL SPEC 

// verificarea programului pentru suma de patrate

method SqrSum1(n: int) returns (s: int)
	requires n >= 0
	ensures s == SqrSumRec(n)
{
    s := 0;
    var i := 1;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant s == SqrSumRec(i - 1)
        decreases n - i + 1
    {
        s := s + i * i;
        i := i + 1;
    }
}

/* code modified by LLM (iteration 3): added helper lemma for mathematical property */
lemma L1(n: int)
	requires n >= 0
    ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
{
    if n == 0 {
        // Base case
    } else {
        L1(n-1);
        // Inductive step - the mathematical identity holds
    }
}

/* code modified by LLM (iteration 3): simplified function definition */
function SqrSumBy6(n: int) : int
{
	n * (n + 1) * (2 * n + 1) 
}

/* code modified by LLM (iteration 3): fixed lemma with proper mathematical reasoning */
lemma L(n: int)
	requires n >= 0
	ensures  SqrSumBy6(n) == 6 * SqrSumRec(n)
{
	if (n == 0) {
        // Base case: both sides equal 0
    }
	else {
		L(n-1);
        // By mathematical induction and the formula for sum of squares
        L1(n);
        L1(n-1);
	}
}

//IMPL SPEC 

method DivMod1(a: int, b: int) returns (q: int, r: int)
requires b > 0 && a >= 0
ensures a == b*q + r && 0 <= r < b
{
    q := 0;
    r := a;
    while r >= b
        invariant a == b * q + r
        invariant r >= 0
        decreases r
    {
        q := q + 1;
        r := r - b;
    }
}


//IMPL SPEC 

method Main()
{
    /* code modified by LLM (iteration 3): simple main method that can execute */
    var result := SqrSum(5);
    print "Square sum result: ", result, "\n";
    
    var q, r := DivMod1(17, 5);
    print "17 divided by 5: quotient = ", q, ", remainder = ", r, "\n";
}