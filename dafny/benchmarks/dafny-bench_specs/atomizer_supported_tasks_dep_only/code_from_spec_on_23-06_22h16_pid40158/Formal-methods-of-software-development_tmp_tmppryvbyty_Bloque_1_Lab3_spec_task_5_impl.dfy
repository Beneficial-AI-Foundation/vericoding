//ATOM factorial
function factorial(n:int):int
requires n>=0
{
    if n==0 || n==1 then 1 else n*factorial(n-1)
}

//IMPL ComputeFact2
method ComputeFact2 (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)
{
    if n == 0 || n == 1 {
        f := 1;
    } else {
        f := 1;
        var i := 2;
        while i <= n
            invariant 1 <= i <= n + 1
            invariant f == factorial(i - 1)
        {
            f := f * i;
            i := i + 1;
        }
    }
}

//ATOM sumSerie
function sumSerie(n:int): int
requires n >= 1
{
    if n == 1 then 1 else sumSerie(n-1) + 2*n - 1
}

//ATOM Sqare_Lemma
lemma Sqare_Lemma (n:int)
requires n>=1
ensures sumSerie(n) == n*n
{
    if n==1 {}
    else{
        Sqare_Lemma(n-1);

        calc == {
            sumSerie(n);
            sumSerie(n-1) + 2*n -1;
            {
                Sqare_Lemma(n-1);
            }
            (n-1)*(n-1) + 2*n -1;
            n*n-2*n+1 +2*n -1;
            n*n;
        }
    }
}