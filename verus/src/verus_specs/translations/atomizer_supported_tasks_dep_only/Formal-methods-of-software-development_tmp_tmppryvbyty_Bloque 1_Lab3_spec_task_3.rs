pub fn multipleReturns3(x: int, y: int) -> (more: int, less: int)
    requires(y > 0)
    ensures(|result: (int, int)| result.0 - result.1 == 2*y)
{
    todo!()
}

pub fn Sqare_Lemma(n: int)
    requires(n >= 1)
    ensures(sumSerie(n) == n*n)
{
    todo!()
}