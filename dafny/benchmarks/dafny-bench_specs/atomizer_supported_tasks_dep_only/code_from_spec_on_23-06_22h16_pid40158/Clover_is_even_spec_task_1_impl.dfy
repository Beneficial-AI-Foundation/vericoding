//IMPL 
method ComputeIsEven(x:int) returns (is_even:bool)
  ensures (x % 2 == 0)==is_even
{
  is_even := x % 2 == 0;
}