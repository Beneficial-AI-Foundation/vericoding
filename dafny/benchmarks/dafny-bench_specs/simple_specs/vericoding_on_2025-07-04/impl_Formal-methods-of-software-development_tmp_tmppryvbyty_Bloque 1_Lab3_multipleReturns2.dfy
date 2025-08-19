//IMPL 
method multipleReturns2 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more + less == 2*x
{
    /* code modified by LLM (iteration 1): implementation already correct, no changes needed */
    more := 2*x;
    less := 0;
}