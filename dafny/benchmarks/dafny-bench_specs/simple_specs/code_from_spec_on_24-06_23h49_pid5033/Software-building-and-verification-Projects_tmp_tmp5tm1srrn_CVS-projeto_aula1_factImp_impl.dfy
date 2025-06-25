//IMPL 
method factImp(n: int) returns (r: int)
{
    if n <= 1 {
        r := 1;
    } else {
        var i := 1;
        r := 1;
        while i <= n 
        {
            r := r * i;
            i := i + 1;
        }
    }
}