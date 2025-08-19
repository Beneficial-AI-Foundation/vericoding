//IMPL
method CalDiv() returns (x:int, y:int)
 ensures x==191/7
 ensures y==191%7
{
    x := 191/7;
    y := 191%7;
}