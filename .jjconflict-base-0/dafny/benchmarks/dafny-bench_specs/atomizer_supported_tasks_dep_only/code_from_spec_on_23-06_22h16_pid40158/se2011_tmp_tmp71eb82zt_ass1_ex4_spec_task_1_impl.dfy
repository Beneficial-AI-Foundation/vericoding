//IMPL 
method Eval(x:int) returns (r:int)
requires x >= 0
ensures r == x*x
{
    r := x * x;
}