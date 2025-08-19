//IMPL
method Cube(n: nat) returns (c: nat) 
  ensures c == n * n * n
{
  c := n * n * n;
}