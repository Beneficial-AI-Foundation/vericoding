//IMPL SqrSum
method SqrSum(n: int) returns (s: int)
{
    s := 0;
    var i := 1;
    while i <= n
    {
        s := s + i * i;
        i := i + 1;
    }
}