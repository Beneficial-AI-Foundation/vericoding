//ATOM multipleReturns
method multipleReturns(x: int, y: int) returns (a: int, b: int)
{
    a := x + y;
    b := x - y;
}

//ATOM multipleReturns2
method multipleReturns2(x: int, y: int) returns (a: int, b: int)
{
    return x + y, x - y;
}

//ATOM multipleReturns3
method multipleReturns3(x: int, y: int) returns (a: int, b: int)
{
    a, b := x + y, x - y;
}

//ATOM factorial
function factorial(n: int): int
    requires n >= 0
{
    if n == 0 then 1 else n * factorial(n - 1)
}

//ATOM ComputeFact
method ComputeFact(n: int) returns (f: int)
    requires n >= 0
    ensures f == factorial(n)
{
    f := 1;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant f == factorial(i - 1)
    {
        f := f * i;
        i := i + 1;
    }
}

//ATOM ComputeFact2
method ComputeFact2(n: int) returns (f: int)
    requires n >= 0
    ensures f == factorial(n)
{
    if n == 0 {
        f := 1;
    } else {
        var temp := ComputeFact2(n - 1);
        f := n * temp;
    }
}

//IMPL Sqare
method Sqare(a: int) returns (x: int)
    requires a >= 1
    ensures x == a * a
{
    x := a * a;
}

//ATOM sumSerie
function sumSerie(n: int): int
    requires n >= 1
{
    if n == 1 then 1 else sumSerie(n - 1) + 2 * n - 1
}

//ATOM Sqare_Lemma
lemma Sqare_Lemma(n: int)
    requires n >= 1
    ensures sumSerie(n) == n * n
{
    if n == 1 {
    } else {
        Sqare_Lemma(n - 1);

        calc == {
            sumSerie(n);
            sumSerie(n - 1) + 2 * n - 1;
            {
                Sqare_Lemma(n - 1);
            }
            (n - 1) * (n - 1) + 2 * n - 1;
            n * n - 2 * n + 1 + 2 * n - 1;
            n * n;
        }
    }
}