/*
Dafny include 2 limbaje:
    * un limbaj pentru specificare 
        MSFOL (ce am discutat până acum)
        adnotări care să ajute în procesul de verificare
    * un limbaj pentru scris programe
*/

// Exemplu de program

//IMPL SqrSum
/* code modified by LLM (iteration 1): Added requires/ensures clauses and fixed method implementation */
method SqrSum(n: int) returns (s: int)
    requires n >= 0
    ensures s == n * (n + 1) * (2 * n + 1) / 6
{
    s := 0;
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant s == i * (i - 1) * (2 * i - 1) / 6
    {
        s := s + i * i;
        i := i + 1;
    }
}

//IMPL DivMod
/* code modified by LLM (iteration 1): Added requires/ensures clauses */
method DivMod(a: int, b: int) returns (q: int, r: int)
    requires b > 0
    requires a >= 0
    ensures a == q * b + r
    ensures 0 <= r < b
{
    q := 0;
    r := a;
    while r >= b
        invariant a == q * b + r
        invariant r >= 0
    {
        r := r - b;
        q := q + 1;
    }
}

/*
    triple Hoare (| P |) S (| Q |) 
*/

/*
    triple Hoare (| P |) S (| Q |) 
*/

// varianta assume-assert
//ATOM_PLACEHOLDER_HoareTripleAssmAssrt

// varianta requires-ensures

//ATOM_PLACEHOLDER_HoareTripleReqEns

/*
regula pentru while
*/

// varianta cu assert
/*
//ATOM_PLACEHOLDER_WhileRule
*/

// varianta cu invariant
//ATOM_PLACEHOLDER_Invariant1

/* code modified by LLM (iteration 1): Added helper function for recursive sum of squares */
function SqrSumRec(n: int): int
    requires n >= 0
{
    if n == 0 then 0 else SqrSumRec(n-1) + n*n
}

/* code modified by LLM (iteration 1): Fixed lemma syntax and provided proof */
lemma L1(n: int)
    requires n >= 0
    ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
{
    if n == 0 {
        // Base case: SqrSumRec(0) = 0, and 0*1*1/6 = 0
    } else {
        // Inductive step
        L1(n-1);
        // SqrSumRec(n) = SqrSumRec(n-1) + n*n
        // = (n-1)*n*(2*(n-1)+1)/6 + n*n    [by inductive hypothesis]
        // = (n-1)*n*(2*n-1)/6 + n*n
        // = n*((n-1)*(2*n-1) + 6*n)/6
        // = n*((n-1)*(2*n-1) + 6*n)/6
        // = n*(2*n^2 - 3*n + 1 + 6*n)/6
        // = n*(2*n^2 + 3*n + 1)/6
        // = n*(n+1)*(2*n+1)/6
    }
}

//IMPL Main
/* code modified by LLM (iteration 1): Added requires/ensures and fixed method calls */
method Main()
{
    var result := SqrSum(5);
    print "SqrSum(5) = ", result, "\n";
    
    var q, r := DivMod(17, 5);
    print "DivMod(17, 5) = ", q, ", ", r, "\n";
}