//ATOM_PLACEHOLDER_Index

//IMPL 

method Min(x: int, y: int) returns (m: int) 
ensures m <= x && m <= y
ensures m == x || m == y
{
    if x <= y {
        m := x;
    } else {
        m := y;
    }
}


//ATOM_PLACEHOLDER_Max


//ATOM_PLACEHOLDER_MaxSum


//ATOM_PLACEHOLDER_MaxSumCaller

//ATOM_PLACEHOLDER_ReconstructFromMaxSum


//ATOM_PLACEHOLDER_TestMaxSum