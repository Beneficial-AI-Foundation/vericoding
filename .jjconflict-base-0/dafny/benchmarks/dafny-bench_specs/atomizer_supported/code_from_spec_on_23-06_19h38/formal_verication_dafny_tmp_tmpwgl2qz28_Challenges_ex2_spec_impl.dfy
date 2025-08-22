//IMPL 
method Forbid42_1(x:int, y:int) returns (z:int)
requires y != 42;
ensures z == x/(42-y);
{
    z := x / (42 - y);
}

//IMPL 
method Allow42_1(x:int, y:int) returns (z: int, err:bool) 
ensures y != 42 ==> z == x/(42-y) && err == false;
ensures y == 42 ==> z == 0 && err == true;
{
    if y == 42 {
        z := 0;
        err := true;
    } else {
        z := x / (42 - y);
        err := false;
    }
}

//IMPL 
method Forbid42_2(x:int, y:int) returns (z:int)
requires y != 42;
ensures z == x/(42-y);
{
    z := x / (42 - y);
}

//IMPL 
method Allow42_2(x:int, y:int) returns (z: int, err:bool) 
ensures y != 42 ==> z == x/(42-y) && err == false;
ensures y == 42 ==> z == 0 && err == true;
{
    if y == 42 {
        z := 0;
        err := true;
    } else {
        z := x / (42 - y);
        err := false;
    }
}

//IMPL 
method TEST1()
{
}