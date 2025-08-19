//IMPL
// problem 2:
// name:   Gabriele Berardi
// s-number: s4878728
// table:   XXX

method problem2(p:int, q:int, X:int, Y:int) returns (r:int, s:int)
requires p == 2*X + Y && q == X + 3
ensures r == X && s == Y
{
    r := q - 3;
    s := p - 2*q + 6;
}