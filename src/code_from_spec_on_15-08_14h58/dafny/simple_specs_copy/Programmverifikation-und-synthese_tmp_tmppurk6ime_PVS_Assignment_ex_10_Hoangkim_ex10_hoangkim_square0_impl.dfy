//IMPL
//Problem01
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
        sqn := sqn + x;
        i := i + 1;
        x := 2 * i + 1;
    }
}