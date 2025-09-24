// <vc-preamble>
predicate ValidInput(s: string)
{
    |s| > 0 && '\n' in s
}

predicate ValidCoordinates(coords: seq<int>, n: int)
{
    |coords| == n && n >= 1
}

predicate Intersect(a: int, b: int, x: int, y: int)
{
    var min_ab := if a <= b then a else b;
    var max_ab := if a <= b then b else a;
    var min_xy := if x <= y then x else y;
    var max_xy := if x <= y then y else x;

    !(min_ab >= min_xy && max_ab <= max_xy) &&
    !(min_xy >= min_ab && max_xy <= max_ab) &&
    !(max_ab <= min_xy) &&
    !(max_xy <= min_ab)
}

function ExtractCoordinates(s: string): seq<int>
    requires ValidInput(s)
    ensures ValidCoordinates(ExtractCoordinates(s), |ExtractCoordinates(s)|)
{
    assume false; [0]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures result == "yes" || result == "no"
    ensures var coords := ExtractCoordinates(s);
            var n := |coords|;
            result == "yes" <==> (n >= 3 && exists i, j :: 0 <= i < n-1 && i < j < n-1 && 
                                 Intersect(coords[i], coords[i+1], coords[j], coords[j+1]))
    ensures var coords := ExtractCoordinates(s);
            var n := |coords|;
            result == "no" <==> (n < 3 || (forall i, j :: 0 <= i < n-1 && i < j < n-1 ==> 
                                !Intersect(coords[i], coords[i+1], coords[j], coords[j+1])))
// </vc-spec>
// <vc-code>
{
    var coords := ExtractCoordinates(s);
    var n := |coords|;

    if n <= 2 {
        result := "no";
        return;
    }

    var i := 0;
    var foundIntersection := false;

    while i < n - 1 && !foundIntersection
        invariant 0 <= i <= n - 1
        invariant !foundIntersection ==> (forall ii, jj :: 0 <= ii < n-1 && ii < jj < n-1 && ii < i ==> 
                                         !Intersect(coords[ii], coords[ii+1], coords[jj], coords[jj+1]))
        decreases n - 1 - i
    {
        var j := i + 1;
        while j < n - 1 && !foundIntersection
            invariant i + 1 <= j <= n - 1
            invariant !foundIntersection ==> (forall jjj :: i + 1 <= jjj < j ==> 
                                             !Intersect(coords[i], coords[i+1], coords[jjj], coords[jjj+1]))
            decreases n - 1 - j
        {
            if Intersect(coords[i], coords[i+1], coords[j], coords[j+1]) {
                foundIntersection := true;
            }
            j := j + 1;
        }
        i := i + 1;
    }

    result := if foundIntersection then "yes" else "no";
}
// </vc-code>
