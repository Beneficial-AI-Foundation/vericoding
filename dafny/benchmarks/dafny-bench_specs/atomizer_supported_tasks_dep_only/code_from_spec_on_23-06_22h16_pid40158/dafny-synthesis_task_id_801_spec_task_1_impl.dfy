//IMPL 
method CountEqualNumbers(a: int, b: int, c: int) returns (count: int)
    ensures count >= 0 && count <= 3
    ensures (count == 3) <==> (a == b && b == c)
    ensures (count == 2) <==> ((a == b && b != c) || (a != b && b == c) || (a == c && b != c))
    ensures (count == 1) <==> (a != b && b != c && a != c)
{
    if a == b && b == c {
        count := 3;
    } else if (a == b && b != c) || (a != b && b == c) || (a == c && b != c) {
        count := 2;
    } else {
        count := 1;
    }
}