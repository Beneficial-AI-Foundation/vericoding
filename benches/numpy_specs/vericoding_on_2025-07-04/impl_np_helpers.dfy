//IMPL ExampleSpec
method ExampleMethod(x: int) returns (y: int)
requires x >= 0
ensures y >= x
{
    /* code modified by LLM (iteration 1): Added assignment to satisfy postcondition */
    y := x;
}