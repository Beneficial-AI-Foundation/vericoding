//IMPL 
method add_by_inc(x: nat, y: nat) returns (z: nat)
ensures z == x + y
{
    z := x;
    var i := 0;
    while i < y
        invariant 0 <= i <= y
        invariant z == x + i
    {
        z := z + 1;
        i := i + 1;
    }
}