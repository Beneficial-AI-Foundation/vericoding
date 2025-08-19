//IMPL 

method Max(x:int, y:int) returns (a:int)
ensures a == x || a == y
ensures x > y ==> a == x
ensures x <= y ==> a == y
{
    if x > y {
        a := x;
    } else {
        a := y;
    }
}