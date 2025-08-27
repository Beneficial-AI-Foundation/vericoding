// SPEC

method Foo(y: int, x: int) returns (z: int) 
 requires 0 <= y
 ensures z == x*y
{
}
