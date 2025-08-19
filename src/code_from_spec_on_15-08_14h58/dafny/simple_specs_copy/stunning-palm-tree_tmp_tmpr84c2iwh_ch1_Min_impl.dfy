//IMPL 
method Min (x: int, y: int) returns (r: int)
 ensures r <= x && r <= y
 ensures r == x || r == y 
{
    if x <= y {
        r := x;
    } else {
        r := y;
    }
}