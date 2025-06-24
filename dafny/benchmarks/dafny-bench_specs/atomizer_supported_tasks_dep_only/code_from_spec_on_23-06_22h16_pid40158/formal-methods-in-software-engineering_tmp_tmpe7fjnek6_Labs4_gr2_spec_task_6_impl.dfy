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

//ATOM DivMod
method DivMod(x: int, y: int) returns (q: int, r: int)
    requires y > 0
    ensures x == q * y + r && 0 <= r < y
{
    q := 0;
    r := x;
    while r >= y
        invariant x == q * y + r && r >= 0
        decreases r
    {
        q := q + 1;
        r := r - y;
    }
}

/*
    triple Hoare (| P |) S (| Q |) 
*/

// varianta assume-assert
//ATOM HoareTripleAssmAssrt
method HoareTripleAssmAssrt()
{
    assume true; // P
    // S - some statement
    assert true; // Q
}

// varianta requires-ensures

//ATOM HoareTripleReqEns
method HoareTripleReqEns()
    requires true // P
    ensures true  // Q
{
    // S - method body
}

/*
regula pentru while
*/

// varianta cu assert
//ATOM WhileRule
method WhileRule()
{
    var i := 0;
    while i < 10
        invariant 0 <= i <= 10
        decreases 10 - i
    {
        i := i + 1;
    }
}

// varianta cu invariant
//IMPL Invariant1
method Invariant1()
{
    /* code modified by LLM (iteration 1): Added proper implementation with correct loop structure */
    var x := 0;
    while x < 5
        invariant 0 <= x <= 5
        decreases 5 - x
    {
        x := x + 1;
    }
}

//specificarea sumei de patrate
//ATOM SqrSumRec
function SqrSumRec(n: int): int
    requires n >= 0
{
    if n == 0 then 0 else n*n + SqrSumRec(n-1)
}

//ATOM SqrSum1
method SqrSum1(n: int) returns (sum: int)
    requires n >= 0
    ensures sum == SqrSumRec(n)
{
    sum := 0;
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant sum == SqrSumRec(i-1) if i > 0 else 0
        decreases n - i
    {
        sum := sum + i * i;
        i := i + 1;
    }
}

// verificarea programului pentru suma de patrate

// SqrSumRec(n) = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
//ATOM L1
lemma L1(n: int)
	requires n >= 0
    ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
{
    if n == 0 {
        // Base case: SqrSumRec(0) == 0 and 0*(0+1)*(2*0+1)/6 == 0
    } else {
        // Inductive step
        L1(n-1);
        calc == {
            SqrSumRec(n);
            n*n + SqrSumRec(n-1);
            { L1(n-1); }
            n*n + (n-1)*n*(2*(n-1)+1)/6;
            n*n + (n-1)*n*(2*n-1)/6;
            (6*n*n + (n-1)*n*(2*n-1))/6;
            n*(6*n + (n-1)*(2*n-1))/6;
            n*(6*n + 2*n*n - 3*n + 1)/6;
            n*(2*n*n + 3*n + 1)/6;
            n*(n+1)*(2*n+1)/6;
        }
    }
}

//ATOM SqrSumBy6
function SqrSumBy6(n: int): int
    requires n >= 0
{
    if n == 0 then 0 else 6*n*n + SqrSumBy6(n-1)
}

//ATOM DivMod1
method DivMod1(x: int, y: int) returns (q: int, r: int)
    requires y > 0
    ensures x == q * y + r && 0 <= r < y
{
    if x >= 0 {
        q := 0;
        r := x;
        while r >= y
            invariant x == q * y + r && r >= 0
            decreases r
        {
            q := q + 1;
            r := r - y;
        }
    } else {
        q := -1;
        r := x + y;
        while r < 0
            invariant x == q * y + r && r < y
            decreases -r
        {
            q := q - 1;
            r := r + y;
        }
    }
}

//ATOM Main
method Main()
{
    var result := SqrSum(3);
    print "SqrSum(3) = ", result, "\n";
    
    var q, r := DivMod(17, 5);
    print "17 div 5 = ", q, " remainder ", r, "\n";
}