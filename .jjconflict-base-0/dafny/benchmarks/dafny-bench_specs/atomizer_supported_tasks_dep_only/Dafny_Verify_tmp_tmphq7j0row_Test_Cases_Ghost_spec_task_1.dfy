//ATOM_PLACEHOLDER_Average

//ATOM_PLACEHOLDER_Triple

// SPEC 

method Triple1(x: int) returns (r: int)
    ensures r == 3 * x
{
}


// ATOM 

ghost method DoubleQuadruple(x: int) returns (a: int, b: int)
    ensures a == 2 * x && b == 4 * x
{
    a := 2 * x;
    b := 2 * a;
}


//ATOM_PLACEHOLDER_F

//ATOM_PLACEHOLDER_M

//ATOM_PLACEHOLDER_Caller

//ATOM_PLACEHOLDER_MyMethod

