/*
Dafny include 2 limbaje:
    * un limbaj pentru specificare 
        MSFOL (ce am discutat până acum)
        adnotări care să ajute în procesul de verificare
    * un limbaj pentru scris programe
*/

// Exemplu de program



/*
    triple Hoare (| P |) S (| Q |) 
*/

// varianta assume-assert

// varianta requires-ensures


/*
regula pentru while
*/

// varianta cu assert
/*
*/

// varianta cu invariant

//specificarea sumei de patrate
function SqrSumRec(n: int) : int
    requires n >= 0
{
    if (n == 0) then 0 else n*n + SqrSumRec(n-1)
}
/*

*/

// verificarea programului pentru suma de patrate


// SqrSumRec(n) = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
least lemma L1(n: int)
    requires n >= 0
    ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
{
    //OK
}

/*
function SqrSumBy6(n: int) : int
{
    n * (n + 1) * (2 * n + 1) 
}

inductive lemma L(n: int) // it takes a while
    decreases n
    requires n >= 0
    ensures  SqrSumBy6(n) == 6 * SqrSumRec(n)
{
    if (n == 0) {}
    else {
        assert n > 0;
        L(n-1);
        assert SqrSumBy6(n-1) == n*(n-1)*(2*n - 1);
        assert SqrSumBy6(n-1) == 6*SqrSumRec(n-1);
        assert 6*SqrSumRec(n-1) == n*(n-1)*(2*n - 1);
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

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SqrSum1(n: int) returns (s: int)
    requires n >= 0
    ensures s == SqrSumRec(n)  // s = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
// </vc-spec>
// <vc-code>
{
    s := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant s == SqrSumRec(i)
    {
        i := i + 1;
        s := s + i * i;
    }
}
// </vc-code>

