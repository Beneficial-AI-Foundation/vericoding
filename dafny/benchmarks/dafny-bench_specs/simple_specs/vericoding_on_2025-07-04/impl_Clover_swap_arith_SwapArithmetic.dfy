//IMPL 
method SwapArithmetic(X: int, Y: int) returns(x: int, y: int)
 ensures x==Y
 ensures y==X
{
    x := X + Y;
    y := x - Y;
    x := x - y;
}