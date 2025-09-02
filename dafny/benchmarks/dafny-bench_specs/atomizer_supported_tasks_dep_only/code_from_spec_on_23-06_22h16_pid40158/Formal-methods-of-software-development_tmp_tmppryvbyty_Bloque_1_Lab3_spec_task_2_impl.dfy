//IMPL multipleReturns
method multipleReturns2 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more + less == 2*x
{
    more := x + y;
    less := x - y;
}

//ATOM multipleReturns3
method multipleReturns3 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more > x && less < x
{
    more := x + y;
    less := x - y;
}

//ATOM factorial
function factorial(n: nat): nat
{
    if n == 0 then 1 else n * factorial(n - 1)
}

//ATOM ComputeFact
method ComputeFact(n: nat) returns (res: nat)
ensures res == factorial(n)
{
    res := 1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant res == factorial(i)
    {
        i := i + 1;
        res := res * i;
    }
}

//ATOM ComputeFact2
method ComputeFact2(n: nat) returns (res: nat)
ensures res == factorial(n)
{
    if n == 0 {
        res := 1;
    } else {
        res := ComputeFact2(n - 1);
        res := res * n;
    }
}

//ATOM Sqare
function Square(n: int): int
{
    n * n
}

//ATOM sumSerie
function sumSerie(n: int): int
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

//ATOM Sqare2
lemma Sqare2(n: int)
requires n >= 1
ensures sumSerie(n) == n * n
{
    Sqare_Lemma(n);
}