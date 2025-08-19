//IMPL 
method mult(a:int, b:int) returns (x:int)
    requires a >= 0 && b >= 0
    ensures x == a * b
{
    x := 0;
    var i := 0;
    while i < b
        invariant 0 <= i <= b
        invariant x == a * i
    {
        x := x + a;
        i := i + 1;
    }
}