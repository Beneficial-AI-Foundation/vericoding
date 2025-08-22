//IMPL 
method plus_one (x: int) returns (r:int)
 requires x >= 0
 ensures r == x + 1
{
    r := x + 1;
}