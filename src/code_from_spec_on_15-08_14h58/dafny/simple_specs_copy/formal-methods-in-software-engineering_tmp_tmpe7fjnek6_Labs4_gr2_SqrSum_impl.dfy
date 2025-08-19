//IMPL 

// Exemplu de program

method SqrSum(n: int) returns (s: int)
{
    if n <= 0 {
        s := 0;
    } else {
        s := 0;
        var i := 1;
        while i <= n
        {
            s := s + i * i;
            i := i + 1;
        }
    }
}