// SPEC

// 5a
method m1(x: int,y: int) returns (z: int)
 requires 0 < x < y
 ensures z >= 0 && z < y && z != x
{
}
