//IMPL 
method add_by_one (x:int, y:int) returns (r:int)
 requires y >= 0
 ensures r == x + y
{
    r := x + y;
}