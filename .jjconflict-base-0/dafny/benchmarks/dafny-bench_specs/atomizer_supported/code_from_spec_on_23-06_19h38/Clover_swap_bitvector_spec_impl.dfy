//IMPL SwapBitvectors
method SwapBitvectors(X: bv8, Y: bv8) returns(x: bv8, y: bv8)
  ensures x==Y
  ensures y==X
{
  x := Y;
  y := X;
}