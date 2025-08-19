method multipleReturns3 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more - less == 2*y
{
    more := x + y;
    less := x - y;
}