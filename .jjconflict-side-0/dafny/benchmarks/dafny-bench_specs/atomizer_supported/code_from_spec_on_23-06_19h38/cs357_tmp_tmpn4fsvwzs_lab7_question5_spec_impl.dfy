//IMPL 
method M1(x: int, y: int) returns (r: int)
ensures r == x*y
{
    r := x * y;
}

//IMPL 
method A1(x: int, y: int) returns (r: int)
ensures r == x + y
{
    r := x + y;
}