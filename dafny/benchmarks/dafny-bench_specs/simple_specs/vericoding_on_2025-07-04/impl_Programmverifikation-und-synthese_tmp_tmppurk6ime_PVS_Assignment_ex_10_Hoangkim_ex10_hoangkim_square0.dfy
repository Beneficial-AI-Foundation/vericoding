//IMPL
//Problem01
method square0(n:nat) returns (sqn : nat)
ensures sqn == n*n
{
    sqn := 0;
    var i := 0;
    
    while i < n
        invariant i <= n
        invariant sqn == i * i
    {
        var x := 2 * i + 1;
        sqn := sqn + x;
        i := i + 1;
    }
}