pub fn factorial(n: int) -> int
    requires(n >= 0)
{
}

pub fn ComputeFact2(n: int) -> int
    requires(n >= 0)
    ensures(|f: int| f == factorial(n))
{
}

pub fn Sqare_Lemma(n: int)
    requires(n >= 1)
    ensures(sumSerie(n) == n * n)
{
}