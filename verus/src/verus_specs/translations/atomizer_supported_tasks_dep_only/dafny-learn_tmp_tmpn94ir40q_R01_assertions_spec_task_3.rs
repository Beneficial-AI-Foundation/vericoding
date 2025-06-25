pub fn Abs(x: int) -> (y: int)
    ensures(0 <= y)
    ensures(x < 0 ==> y == -x)
    ensures(x >= 0 ==> y == x)
{
}

//ATOM_PLACEHOLDER_TestingAbs

pub fn TestingAbs2()
{
}

//ATOM_PLACEHOLDER_Max
//ATOM_PLACEHOLDER_TestingMax