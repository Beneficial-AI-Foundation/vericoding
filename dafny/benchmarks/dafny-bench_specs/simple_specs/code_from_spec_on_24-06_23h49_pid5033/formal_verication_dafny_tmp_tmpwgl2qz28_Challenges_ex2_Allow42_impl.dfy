//IMPL 
method Allow42(x:int, y:int) returns (z: int, err:bool) 
ensures y != 42 ==> z == x/(42-y) && err == false
ensures y == 42 ==> z == 0 && err == true
{
    if y == 42 {
        z := 0;
        err := true;
    } else {
        z := x / (42 - y);
        err := false;
    }
}