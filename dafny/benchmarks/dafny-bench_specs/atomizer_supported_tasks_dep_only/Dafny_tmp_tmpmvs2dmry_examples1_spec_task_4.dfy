//ATOM_PLACEHOLDER_Abs

//ATOM_PLACEHOLDER_abs

//ATOM_PLACEHOLDER_Testing

//ATOM_PLACEHOLDER_MultiReturn

// SPEC 

method Max(x:int, y:int) returns (a:int)
ensures a == x || a == y;
ensures x > y ==> a == x;
ensures x <= y ==> a == y;
{
}


