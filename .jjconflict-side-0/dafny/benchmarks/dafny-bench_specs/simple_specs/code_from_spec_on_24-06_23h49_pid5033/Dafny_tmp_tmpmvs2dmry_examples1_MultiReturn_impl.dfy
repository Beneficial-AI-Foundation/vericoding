//IMPL 
method MultiReturn(x:int, y:int) returns (more:int, less:int)
requires y>=0
ensures less <= x <= more
{
    less := x - y;
    more := x + y;
}