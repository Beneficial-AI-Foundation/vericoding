//IMPL
method ReconstructFromMaxSum (s: int, m: int ) returns (x: int, y: int)
 // requires (0 < s && s / 2 < m && m < s)
 requires s - m <= m
 ensures s == x + y
 ensures (m == y || m == x) && x <= m && y <= m
{
    x := m;
    y := s - m;
}