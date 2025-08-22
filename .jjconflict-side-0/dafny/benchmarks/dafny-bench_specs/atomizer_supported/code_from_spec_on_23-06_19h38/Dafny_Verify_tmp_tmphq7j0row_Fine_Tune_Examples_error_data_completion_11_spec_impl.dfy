//IMPL main
method main(x :int) returns (j :int, i :int)
requires x > 0
ensures j == 2 * x
{
    j := 2 * x;
    i := 0;
}