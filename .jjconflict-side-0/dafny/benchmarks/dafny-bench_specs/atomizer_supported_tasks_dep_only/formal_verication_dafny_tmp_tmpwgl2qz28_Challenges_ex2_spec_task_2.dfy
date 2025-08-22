/*
    i)  Write a verified method with signature
//ATOM_PLACEHOLDER_Forbid42// SPEC 

method Allow42(x:int, y:int) returns (z: int, err:bool) 
ensures y != 42 ==> z == x/(42-y) && err == false;
ensures y == 42 ==> z == 0 && err == true;
{
}
//ATOM_PLACEHOLDER_Forbid42 

// SPEC 

method Allow42(x:int, y:int) returns (z: int, err:bool) 
ensures y != 42 ==> z == x/(42-y) && err == false;
ensures y == 42 ==> z == 0 && err == true;
{
}


//ATOM_PLACEHOLDER_TEST1

