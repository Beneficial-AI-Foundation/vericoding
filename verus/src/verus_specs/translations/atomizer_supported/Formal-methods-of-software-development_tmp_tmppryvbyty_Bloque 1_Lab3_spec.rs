pub fn multipleReturns(x: int, y: int) -> (more: int, less: int)
    requires(y > 0)
    ensures(|result: (int, int)| result.1 < x < result.0)
{
}

pub fn multipleReturns2(x: int, y: int) -> (more: int, less: int)
    requires(y > 0)
    ensures(|result: (int, int)| result.0 + result.1 == 2*x)
{
}

pub fn multipleReturns3(x: int, y: int) -> (more: int, less: int)
    requires(y > 0)
    ensures(|result: (int, int)| result.0 - result.1 == 2*y)
{
}

spec fn factorial(n: int) -> int
    recommends(n >= 0)
{
    if n == 0 || n == 1 { 1 } else { n * factorial(n-1) }
}

pub fn ComputeFact(n: int) -> (f: int)
    requires(n >= 0)
    ensures(|result: int| result == factorial(n))
{
}

pub fn ComputeFact2(n: int) -> (f: int)
    requires(n >= 0)
    ensures(|result: int| result == factorial(n))
{
}

pub fn Sqare(a: int) -> (x: int)
    requires(a >= 1)
    ensures(|result: int| result == a*a)
{
}

spec fn sumSerie(n: int) -> int
    recommends(n >= 1)
{
    if n == 1 { 1 } else { sumSerie(n-1) + 2*n - 1 }
}

proof fn Sqare_Lemma(n: int)
    requires(n >= 1)
    ensures(sumSerie(n) == n*n)
{
}

pub fn Sqare2(a: int) -> (x: int)
    requires(a >= 1)
    ensures(|result: int| result == a*a)
{
}