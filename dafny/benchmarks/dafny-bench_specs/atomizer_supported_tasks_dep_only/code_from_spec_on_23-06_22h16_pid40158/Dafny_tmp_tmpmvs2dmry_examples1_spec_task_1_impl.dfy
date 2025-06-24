// IMPL 
method Abs(x:int) returns (y:int)
ensures y>=0;
ensures x>=0 ==> x == y;
ensures x<0 ==> -x == y;
ensures y == abs(x); // use this instead of line 3,4
{
    if x < 0 {
        y := -x;
    } else {
        y := x;
    }
}


// ATOM 

function abs(x: int): int{
    if x>0 then x else -x
}


//ATOM_PLACEHOLDER_Testing

//ATOM_PLACEHOLDER_MultiReturn

//ATOM_PLACEHOLDER_Max