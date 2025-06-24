/*
    i)  Write a verified method with signature
// SPEC 

method Forbid42(x:int, y:int) returns (z:int)
requires y != 42;
ensures z == x/(42-y);
{
}
//ATOM_PLACEHOLDER_Allow42// SPEC 

method Forbid42(x:int, y:int) returns (z:int)
requires y != 42;
ensures z == x/(42-y);
{
}
 

//ATOM_PLACEHOLDER_Allow42

//ATOM_PLACEHOLDER_TEST1

