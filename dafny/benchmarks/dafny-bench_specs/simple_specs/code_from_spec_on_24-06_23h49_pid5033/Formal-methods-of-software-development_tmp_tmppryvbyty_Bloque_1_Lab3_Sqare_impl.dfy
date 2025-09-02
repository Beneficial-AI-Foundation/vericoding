//IMPL Sqare

method Sqare(a:int) returns (x:int)
requires a>=1
ensures x == a*a
{
    x := a * a;
}