//IMPL 
method DivMod1(a: int, b: int) returns (q: int, r: int)
requires b > 0 && a >= 0
ensures a == b*q + r && 0 <= r < b
//decreases *
{
    q := 0;
    r := a;
    
    while r >= b
        invariant a == b*q + r
        invariant r >= 0
        decreases r
    {
        q := q + 1;
        r := r - b;
    }
}