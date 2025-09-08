Given a rectangle with vertices at (0,0) and (x,y), find two points A=(x₁,y₁) and C=(x₂,y₂) 
such that triangle ABC with B=(0,0) is right-angled and isosceles at B, contains the entire 
rectangle, has minimum area, and all coordinates are integers with x₁ < x₂.

predicate ValidInput(x: int, y: int)
{
    x != 0 && y != 0
}

predicate ValidOutput(result: seq<int>, x: int, y: int)
{
    |result| == 4 &&
    result[0] < result[2] &&
    (x * y > 0 && x < 0 ==> result == [x + y, 0, 0, x + y]) &&
    (x * y > 0 && x >= 0 ==> result == [0, x + y, x + y, 0]) &&
    (x * y <= 0 && x < 0 ==> result == [x - y, 0, 0, y - x]) &&
    (x * y <= 0 && x >= 0 ==> result == [0, y - x, x - y, 0])
}

method solve(x: int, y: int) returns (result: seq<int>)
    requires ValidInput(x, y)
    ensures ValidOutput(result, x, y)
{
    var x1, y1, x2, y2: int;

    if x * y > 0 {
        if x < 0 {
            x1, y1, x2, y2 := x + y, 0, 0, x + y;
        } else {
            x1, y1, x2, y2 := 0, x + y, x + y, 0;
        }
    } else {
        if x < 0 {
            x1, y1, x2, y2 := x - y, 0, 0, y - x;
        } else {
            x1, y1, x2, y2 := 0, y - x, x - y, 0;
        }
    }

    result := [x1, y1, x2, y2];
}
