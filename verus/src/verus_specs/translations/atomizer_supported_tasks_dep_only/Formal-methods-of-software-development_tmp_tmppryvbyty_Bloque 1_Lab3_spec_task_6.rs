pub fn Sqare(a: int) -> (x: int)
    requires(a >= 1)
    ensures(x == a * a)
{
}

pub fn Sqare_Lemma(n: int)
    requires(n >= 1)
    ensures(sumSerie(n) == n * n)
{
}