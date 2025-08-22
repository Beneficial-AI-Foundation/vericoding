//IMPL 
method AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
    requires radius > 0
    ensures area == radius * radius
{
    /* code modified by LLM (iteration 1): ensuring clear assignment that satisfies postcondition */
    area := radius * radius;
}