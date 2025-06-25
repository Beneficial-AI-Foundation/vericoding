//IMPL 
method Fact(x: int) returns (y: int)
 requires x >= 0;  
{
    if x == 0 {
        y := 1;
    } else {
        var i := 1;
        y := 1;
        while i <= x
            invariant 1 <= i <= x + 1
            invariant y == factorial(i - 1)
        {
            y := y * i;
            i := i + 1;
        }
    }
}

function factorial(n: int): int
    requires n >= 0
{
    if n == 0 then 1 else n * factorial(n - 1)
}