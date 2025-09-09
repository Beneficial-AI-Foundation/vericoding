//ATOM multipleReturns
function multipleReturns(x: int): int { x * 2 }

//ATOM multipleReturns2  
function multipleReturns2(x: int): int { x + 1 }

//ATOM multipleReturns3
function multipleReturns3(x: int): int { x - 1 }

//ATOM factorial
function factorial(n: int): int 
requires n >= 0
{
    if n == 0 then 1 else n * factorial(n-1)
}

// PROGRAMA VERIFICADOR DE WHILE
//ATOM ComputeFact
method ComputeFact(n: int) returns (result: int)
requires n >= 0
ensures result == factorial(n)
{
    result := 1;
    var i := 0;
    while i < n
    invariant 0 <= i <= n
    invariant result == factorial(i)
    {
        i := i + 1;
        result := result * i;
    }
}

//ATOM ComputeFact2
method ComputeFact2(n: int) returns (result: int)
requires n >= 0  
ensures result == factorial(n)
{
    if n == 0 {
        result := 1;
    } else {
        result := ComputeFact2(n-1);
        result := result * n;
    }
}

// n>=1 ==> 1 + 3 + 5 + ... + (2*n-1) = n*n

//ATOM Sqare
method Sqare(a: int) returns (x: int)
requires a >= 1
ensures x == a * a
{
    x := 0;
    var i := 1;
    while i <= a
    invariant 1 <= i <= a + 1
    invariant x == sumSerie(i-1)
    {
        x := x + 2*i - 1;
        i := i + 1;
    }
}

//ATOM sumSerie
function sumSerie(n: int): int
requires n >= 0
{
    if n == 0 then 0 else sumSerie(n-1) + 2*n - 1
}

//ATOM Sqare_Lemma
lemma Sqare_Lemma(n: int)
requires n >= 1
ensures sumSerie(n) == n*n
{
    if n == 1 {}
    else {
        Sqare_Lemma(n-1);

        calc == {
            sumSerie(n);
            sumSerie(n-1) + 2*n - 1;
            {
                Sqare_Lemma(n-1);
            }
            (n-1)*(n-1) + 2*n - 1;
            n*n - 2*n + 1 + 2*n - 1;
            n*n;
        }
    }
}

//IMPL Sqare2
method Sqare2(a: int) returns (x: int)
requires a >= 1
ensures x == a*a
{
    x := 0;
    var i := 1;
    while i <= a
    invariant 1 <= i <= a + 1
    invariant x == sumSerie(i-1)
    {
        x := x + 2*i - 1;
        i := i + 1;
    }
    /* code modified by LLM (iteration 1): Added lemma call to establish final postcondition */
    Sqare_Lemma(a);
}