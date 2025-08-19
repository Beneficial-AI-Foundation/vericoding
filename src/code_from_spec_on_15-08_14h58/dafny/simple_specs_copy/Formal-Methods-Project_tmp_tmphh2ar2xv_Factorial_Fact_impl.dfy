//IMPL 
method Fact(x: int) returns (y: int)
/* code modified by LLM (iteration 1): removed unnecessary semicolon after requires clause */
 requires x >= 0
{
    if x == 0 {
        y := 1;
    } else {
        var temp := Fact(x - 1);
        y := x * temp;
    }
}