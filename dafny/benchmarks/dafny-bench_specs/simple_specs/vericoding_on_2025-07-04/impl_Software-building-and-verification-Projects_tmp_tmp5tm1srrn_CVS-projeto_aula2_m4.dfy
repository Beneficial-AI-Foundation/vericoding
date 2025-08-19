//IMPL 

// 5d
method m4(x: int,y: int) returns (z: bool)
 ensures z ==> x==y && x==y ==> z
{
    z := x == y;
}