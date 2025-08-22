//IMPL Forbid42
method Forbid42(x:int, y:int) returns (z:int)
requires y != 42;
ensures z == x/(42-y);
{
    z := x / (42 - y);
}

//IMPL Allow42
method Allow42(x:int, y:int) returns (z: int, err:bool) 
ensures y != 42 ==> z == x/(42-y) && err == false;
ensures y == 42 ==> z == 0 && err == true;
{
    /* code modified by LLM (iteration 1): Fixed compilation error by removing duplicate method definitions */
    if y == 42 {
        z := 0;
        err := true;
    } else {
        z := x / (42 - y);
        err := false;
    }
}

//IMPL TEST1
method TEST1()
{
}