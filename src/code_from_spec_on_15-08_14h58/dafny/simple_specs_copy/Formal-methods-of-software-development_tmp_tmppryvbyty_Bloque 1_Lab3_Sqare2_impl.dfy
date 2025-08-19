//IMPL 
method Sqare2(a:int) returns (x:int)
requires a>=1
ensures x == a*a
{
    x := a * a;
}