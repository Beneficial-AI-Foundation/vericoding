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
method ComputeFact (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)
// </vc-spec>
// <vc-code>
{
    assert 0 <= n <= n && 1*factorial(n) == factorial(n);
    f:=1;
    assert 0 <= n <= n && f*factorial(n) == factorial(n);
    var x:=n;
    assert 0 <= x <= n && f*factorial(x) == factorial(n);
    while x > 0 
        invariant 0 <= x <= n;
        invariant f*factorial(x)== factorial(n);
        decreases x-0;
    {
        assert 0 <= x-1 <= n && (f*x)*factorial(x-1) == factorial(n);
        f:= f*x;
        assert 0 <= x-1 <= n && f*factorial(x-1) == factorial(n);
        x:=x-1;
        assert 0 <= x <= n && f*factorial(x) == factorial(n);
    }
    assert 0 <= x <= n && f*factorial(x) == factorial(n);
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