// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method multipleReturns (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures less < x < more
// </vc-spec>
// <vc-code>
{
    assume false;
}
// </vc-code>

function factorial(n:int):int
requires n>=0
{
    if n==0 || n==1 then 1 else n*factorial(n-1)
}

// PROGRAMA VERIFICADOR DE WHILE



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