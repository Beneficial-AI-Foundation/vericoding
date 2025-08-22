//IMPL 
method Max(a: int, b: int) returns (c: int)
 ensures c >= a
 ensures c >= b
{
    if a >= b {
        c := a;
    } else {
        c := b;
    }
}