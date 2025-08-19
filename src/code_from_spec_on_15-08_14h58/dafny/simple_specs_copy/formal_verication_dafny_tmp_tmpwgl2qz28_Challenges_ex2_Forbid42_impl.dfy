//IMPL 
method Forbid42(x:int, y:int) returns (z:int)
requires y != 42
ensures z == x/(42-y)
{
    z := x / (42 - y);
}