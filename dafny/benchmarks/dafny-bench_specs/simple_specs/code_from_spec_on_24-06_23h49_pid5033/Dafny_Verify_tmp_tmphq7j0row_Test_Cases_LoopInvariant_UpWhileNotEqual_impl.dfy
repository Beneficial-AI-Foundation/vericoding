//IMPL 

method UpWhileNotEqual(N: int) returns (i: int)
requires 0 <= N
ensures i == N
{
    i := N;
}