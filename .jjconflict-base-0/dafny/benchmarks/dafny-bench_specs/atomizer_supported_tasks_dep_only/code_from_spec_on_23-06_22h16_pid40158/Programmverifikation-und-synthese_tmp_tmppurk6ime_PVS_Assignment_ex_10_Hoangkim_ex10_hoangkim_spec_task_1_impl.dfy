//IMPL Problem01
method square0(n:nat) returns (sqn : nat)
ensures sqn == n*n
{
    sqn := 0;
    var i := 0;
    var x := 1;
    
    while i < n
        invariant 0 <= i <= n
        invariant sqn == i * i
        invariant x == 2 * i + 1
    {
        /* code modified by LLM (iteration 2): fixed invariant maintenance by updating in correct order */
        sqn := sqn + x;
        i := i + 1;
        x := x + 2;
    }
}

//ATOM square1
method square1(n:nat) returns (sqn : nat)
ensures sqn == n*n
{
    sqn := n * n;
}

//ATOM q
method q(x: nat, y: nat) returns (c: nat)
requires y > x + 2
ensures x < c * c < y
{
    c := x + 1;
}

//ATOM strange
method strange()
ensures 1 == 2
{
    var x: nat := 4;
    var c := q(x, 2*x);
}

//ATOM test0
method test0(x: int)
{
    assume x * x < 100;
    assert x <= 9;
}