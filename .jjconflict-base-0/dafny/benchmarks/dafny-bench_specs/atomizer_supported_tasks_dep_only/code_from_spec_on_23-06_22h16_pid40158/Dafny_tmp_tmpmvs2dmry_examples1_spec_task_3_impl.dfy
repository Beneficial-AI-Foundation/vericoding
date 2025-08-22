//ATOM_PLACEHOLDER_Abs

//ATOM_PLACEHOLDER_abs

//ATOM_PLACEHOLDER_Testing

//IMPL MultiReturn
method MultiReturn(x:int, y:int) returns (more:int, less:int)
requires y>=0;
ensures less <= x <= more;
{
    less := x - y;
    more := x + y;
}

//ATOM_PLACEHOLDER_Max