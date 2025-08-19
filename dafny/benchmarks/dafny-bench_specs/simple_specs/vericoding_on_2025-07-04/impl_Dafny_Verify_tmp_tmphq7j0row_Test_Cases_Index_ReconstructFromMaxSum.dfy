//IMPL 
method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
  requires s <= 2 * m
  ensures s == (x + y)
  ensures (m == x || m == y) && x <= m && y <= m
{
  x := m;
  y := s - m;
}