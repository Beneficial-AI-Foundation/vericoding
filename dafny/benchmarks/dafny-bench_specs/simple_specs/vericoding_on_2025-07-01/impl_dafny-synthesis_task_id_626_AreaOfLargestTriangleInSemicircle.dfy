However, the postcondition requires `area == radius * radius`, which suggests we want the result as an integer equal to radius². This makes sense if we're working with integer arithmetic and want the area to be radius².

//IMPL
method AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
  requires radius > 0
  ensures area == radius * radius
{
  area := radius * radius;
}