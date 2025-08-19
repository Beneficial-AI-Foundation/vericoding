//IMPL 
method max(a: int, b: int) returns (z: int)
 requires true
 ensures z >= a || z >= b
{
    if a >= b {
        z := a;
    } else {
        z := b;
    }
}