//ATOM multipleReturns
method multipleReturns (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more > less;
{
    more := x + y;
    less := x - y;
}

//ATOM multipleReturns2
method multipleReturns2 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more > less;
{
    more := x + y;
    less := x;
}

//IMPL multipleReturns3
method multipleReturns3 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more - less == 2*y
{
    more := x + y;
    less := x - y;
    /* code modified by LLM (iteration 1): added assertion to help Dafny verify the arithmetic equivalence */
    assert more - less == (x + y) - (x - y);
    assert (x + y) - (x - y) == x + y - x + y;
    assert x + y - x + y == 2*y;
}

//ATOM factorial
function factorial(n: int): int
requires n >= 0
{
    if n == 0 then 1 else n * factorial(n-1)
}

//ATOM ComputeFact
method ComputeFact(n: int) returns (res: int)
requires n >= 0
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
method ComputeFact2(n: int) returns (res: int)
requires n >= 0
ensures res == factorial(n)
{
    if n == 0 {
        res := 1;
    } else {
        var temp := ComputeFact2(n-1);
        res := n * temp;
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
method Sqare2(n: int) returns (res: int)
requires n >= 1
ensures res == n * n
{
    res := 0;
    var i := 1;
    while i <= n
        /* code modified by LLM (iteration 1): simplified loop invariants to handle the edge case when i == 1 */
        invariant 1 <= i <= n + 1
        invariant i == 1 ==> res == 0
        invariant i > 1 ==> res == sumSerie(i-1)
    {
        res := res + 2*i - 1;
        i := i + 1;
    }
    Sqare_Lemma(n);
}