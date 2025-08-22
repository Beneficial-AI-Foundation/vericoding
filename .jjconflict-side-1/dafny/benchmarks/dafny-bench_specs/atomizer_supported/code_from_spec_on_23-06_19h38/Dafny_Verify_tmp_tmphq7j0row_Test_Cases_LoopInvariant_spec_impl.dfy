//IMPL UpWhileLess
method UpWhileLess(N: int) returns (i: int)
requires 0 <= N
ensures i == N
{
    i := 0;
    while i < N
        invariant 0 <= i <= N
    {
        i := i + 1;
    }
}

//IMPL UpWhileNotEqual
method UpWhileNotEqual(N: int) returns (i: int)
requires 0 <= N
ensures i == N
{
    i := 0;
    while i != N
        invariant 0 <= i <= N
    {
        i := i + 1;
    }
}

//IMPL DownWhileNotEqual
method DownWhileNotEqual(N: int) returns (i: int)
requires 0 <= N
ensures i == 0
{
    i := N;
    while i != 0
        invariant 0 <= i <= N
    {
        i := i - 1;
    }
}

//IMPL DownWhileGreater
method DownWhileGreater(N: int) returns (i: int)
requires 0 <= N
ensures i == 0
{
    i := N;
    while i > 0
        invariant 0 <= i <= N
    {
        i := i - 1;
    }
}

//IMPL Quotient
method Quotient()
{
}

//IMPL Quotient1
method Quotient1() 
{
}