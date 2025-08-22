//ATOM_PLACEHOLDER_Index

//ATOM_PLACEHOLDER_Min

//ATOM_PLACEHOLDER_Max


//ATOM_PLACEHOLDER_MaxSum


//ATOM_PLACEHOLDER_MaxSumCaller

//IMPL ReconstructFromMaxSum
method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
    requires s <= 2 * m
    ensures s == (x + y)
    ensures (m == x || m == y) && x <= m && y <= m
{
    x := m;
    y := s - m;
}

//ATOM_PLACEHOLDER_TestMaxSum