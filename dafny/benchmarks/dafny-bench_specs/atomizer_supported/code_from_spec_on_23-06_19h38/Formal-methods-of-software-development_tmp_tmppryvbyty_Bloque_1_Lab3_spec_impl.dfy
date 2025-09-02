//IMPL multipleReturns
method multipleReturns (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures less < x < more
{
    /* code modified by LLM (iteration 1): Added assertion to help verify the postcondition */
    more := x + y;
    less := x - y;
    assert less == x - y < x < x + y == more;
}

//IMPL multipleReturns2
method multipleReturns2 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more + less == 2*x
{
    more := x + y;
    less := x - y;
    /* code modified by LLM (iteration 1): Added assertion to verify arithmetic */
    assert more + less == (x + y) + (x - y) == 2*x;
}

//IMPL multipleReturns3
method multipleReturns3 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more - less == 2*y
{
    more := x + y;
    less := x - y;
    /* code modified by LLM (iteration 1): Added assertion to verify arithmetic */
    assert more - less == (x + y) - (x - y) == 2*y;
}

//ATOM factorial
function factorial(n:int):int
requires n>=0
{
    if n==0 || n==1 then 1 else n*factorial(n-1)
}

//IMPL ComputeFact
method ComputeFact (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)
{
    f := 1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant f == factorial(i)
    {
        i := i + 1;
        f := f * i;
    }
}

//IMPL ComputeFact2
method ComputeFact2 (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)
/* code modified by LLM (iteration 1): Added decreases clause for termination */
decreases n
{
    if n == 0 || n == 1 {
        f := 1;
    } else {
        var temp := ComputeFact2(n - 1);
        f := n * temp;
    }
}

//IMPL Sqare
method Sqare(a:int) returns (x:int)
requires a>=1
ensures x == a*a
{
    x := 0;
    var i := 1;
    /* code modified by LLM (iteration 1): Fixed loop invariant to handle base case properly */
    while i <= a
        invariant 1 <= i <= a + 1
        invariant i == 1 ==> x == 0
        invariant i > 1 ==> x == sumSerie(i - 1)
    {
        x := x + (2 * i - 1);
        i := i + 1;
    }
    /* code modified by LLM (iteration 1): Added assertion before calling lemma */
    assert i == a + 1;
    assert x == sumSerie(a);
    Sqare_Lemma(a);
}

//ATOM sumSerie
function sumSerie(n:int):int
requires n >=1 
{
    if n==1 then 1 else sumSerie(n-1) + 2*n -1
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

//IMPL Sqare2
method Sqare2(a:int) returns (x:int)
requires a>=1
ensures x == a*a
{
    x := a * a;
}