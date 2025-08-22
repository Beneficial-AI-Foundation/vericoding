//IMPL
method ReconstructFromMaxSum (s: int, m: int ) returns (x: int, y: int)
 // requires (0 < s && s / 2 < m && m < s)
 requires s - m <= m
 ensures s == x + y
 ensures (m == y || m == x) && x <= m && y <= m
{
    x := m;
    y := s - m;
    /* code modified by LLM (iteration 1): Added assertion to help Dafny verify that y <= m follows from the precondition */
    assert y <= m; // This follows from y = s - m and precondition s - m <= m
}