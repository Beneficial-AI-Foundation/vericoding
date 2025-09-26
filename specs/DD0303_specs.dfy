// <vc-preamble>
function factorial(n: nat): nat
{
    if n == 0 then 1 else n * factorial(n-1)
}



// PROGRAMA VERIFICADOR DE WHILE
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method ComputeFact2 (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)
// </vc-spec>
// <vc-code>
{
    var x:= 0;
    f:= 1;
    while x<n
        invariant 0<=x<=n;
        invariant f==factorial(x);
        decreases n - x;
    {
        x:=x+1;
        f:= f*x;
        assert 0<=x<=n && f==factorial(x);  
    }
}
// </vc-code>

// n>=1 ==> 1 + 3 + 5 + ... + (2*n-1) = n*n



function sumSerie(n:int):int
requires n >=1 
{
    if n==1 then 1 else sumSerie(n-1) + 2*n -1
}

lemma Sqare_Lemma (n:int)
requires n>=1
ensures sumSerie(n) == n*n
{
    if n==1 {}
    else{
        Sqare_Lemma(n-1);
        assert sumSerie(n-1) ==(n-1)*(n-1);

        calc == {
            sumSerie(n);
            sumSerie(n-1) + 2*n -1;
            {
                Sqare_Lemma(n-1);
                assert sumSerie(n-1) ==(n-1)*(n-1);
            }
            (n-1)*(n-1) + 2*n -1;
            n*n-2*n+1 +2*n -1;
            n*n;
        }
    assert sumSerie(n) == n*n;
    }
}