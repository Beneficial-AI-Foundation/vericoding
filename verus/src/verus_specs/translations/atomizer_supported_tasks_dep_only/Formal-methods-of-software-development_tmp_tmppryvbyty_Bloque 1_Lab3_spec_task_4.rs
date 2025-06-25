pub fn factorial(n: int) -> int
    requires(n >= 0)
{
}

pub fn ComputeFact(n: int) -> f: int
    requires(n >= 0)
    ensures(f == factorial(n))
{
}

pub fn ComputeFact(n: int) -> f: int
    requires(n >= 0)
    ensures(f == factorial(n))
{
}

pub fn Sqare_Lemma(n: int)
    requires(n >= 1)
    ensures(sumSerie(n) == n * n)
{
}