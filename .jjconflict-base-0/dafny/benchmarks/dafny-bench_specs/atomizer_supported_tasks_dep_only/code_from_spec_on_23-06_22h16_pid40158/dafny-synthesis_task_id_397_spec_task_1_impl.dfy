//IMPL MedianOfThree
method MedianOfThree(a: int, b: int, c: int) returns (median: int)
    ensures median == a || median == b || median == c
    ensures (median >= a && median <= b) || (median >= b && median <= a) || (median >= a && median <= c) || (median >= c && median <= a) || (median >= b && median <= c) || (median >= c && median <= b)
{
    if a <= b && b <= c {
        median := b;
    } else if a <= c && c <= b {
        median := c;
    } else if b <= a && a <= c {
        median := a;
    } else if b <= c && c <= a {
        median := c;
    } else if c <= a && a <= b {
        median := a;
    } else {
        median := b;
    }
}