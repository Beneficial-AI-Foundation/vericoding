//IMPL 
method DownWhileNotEqual(N: int) returns (i: int)
requires 0 <= N
ensures i == 0
{
    i := N;
    while i != 0
        invariant 0 <= i
        decreases i
    {
        i := i - 1;
    }
}