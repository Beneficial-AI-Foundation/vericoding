// <vc-preamble>
predicate ValidInput(n: int, x1: int, y1: int, x2: int, y2: int, flowers: seq<(int, int)>)
{
    && n >= 1
    && n == |flowers|
    && n <= 2000
    && -10000000 <= x1 <= 10000000
    && -10000000 <= y1 <= 10000000
    && -10000000 <= x2 <= 10000000
    && -10000000 <= y2 <= 10000000
    && (forall i :: 0 <= i < |flowers| ==> 
        -10000000 <= flowers[i].0 <= 10000000 && -10000000 <= flowers[i].1 <= 10000000)
    && (forall i, j :: 0 <= i < j < |flowers| ==> flowers[i] != flowers[j])
    && (forall i :: 0 <= i < |flowers| ==> flowers[i] != (x1, y1) && flowers[i] != (x2, y2))
    && (x1, y1) != (x2, y2)
}

function SquaredDistance(x1: int, y1: int, x2: int, y2: int): int
{
    (x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2)
}

predicate FlowersCoverable(r1Squared: int, r2Squared: int, x1: int, y1: int, x2: int, y2: int, flowers: seq<(int, int)>)
{
    forall i :: 0 <= i < |flowers| ==> 
        SquaredDistance(flowers[i].0, flowers[i].1, x1, y1) <= r1Squared ||
        SquaredDistance(flowers[i].0, flowers[i].1, x2, y2) <= r2Squared
}
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int
{
    if a > b then a else b
}

function min(a: int, b: int): int
{
    if a < b then a else b
}

method sortByFirst(arr: seq<(int, int)>) returns (sorted: seq<(int, int)>)
    requires |arr| >= 0
    requires forall i :: 0 <= i < |arr| ==> arr[i].0 >= 0 && arr[i].1 >= 0
    ensures |sorted| == |arr|
    ensures multiset(sorted) == multiset(arr)
    ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i].0 <= sorted[j].0
    ensures forall i :: 0 <= i < |sorted| ==> sorted[i].0 >= 0 && sorted[i].1 >= 0
{
    sorted := arr;
    var n := |arr|;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |sorted| == n
        invariant multiset(sorted) == multiset(arr)
        invariant forall x, y :: 0 <= x < y < i ==> sorted[x].0 <= sorted[y].0
        invariant forall x, y :: 0 <= x < i <= y < n ==> sorted[x].0 <= sorted[y].0
        invariant forall j :: 0 <= j < |sorted| ==> sorted[j].0 >= 0 && sorted[j].1 >= 0
    {
        var minIdx := i;
        var j := i + 1;
        while j < n
            invariant i <= minIdx < n
            invariant i < j <= n
            invariant |sorted| == n
            invariant multiset(sorted) == multiset(arr)
            invariant forall k :: i <= k < j ==> sorted[minIdx].0 <= sorted[k].0
        {
            if sorted[j].0 < sorted[minIdx].0
            {
                minIdx := j;
            }
            j := j + 1;
        }

        if minIdx != i {
            var temp := sorted[i];
            sorted := sorted[i := sorted[minIdx]];
            sorted := sorted[minIdx := temp];
        }
        i := i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, x1: int, y1: int, x2: int, y2: int, flowers: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, x1, y1, x2, y2, flowers)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    // Calculate squared distances for each flower to both fountains
    var distances: seq<(int, int)> := [];
    var i := 0;
    while i < |flowers|
        invariant 0 <= i <= |flowers|
        invariant |distances| == i
        invariant forall j :: 0 <= j < i ==> distances[j].0 >= 0 && distances[j].1 >= 0
    {
        var flower := flowers[i];
        var d1 := (flower.0 - x1) * (flower.0 - x1) + (flower.1 - y1) * (flower.1 - y1);
        var d2 := (flower.0 - x2) * (flower.0 - x2) + (flower.1 - y2) * (flower.1 - y2);
        distances := distances + [(d1, d2)];
        i := i + 1;
    }

    // Sort distances by first component (distance to fountain 1)
    distances := sortByFirst(distances);

    // Create maxtaild array - suffix maximum of distances to fountain 2
    var maxtaild := new int[n + 1];
    maxtaild[n] := 0;
    i := n - 1;
    while i >= 0
        invariant -1 <= i <= n - 1
        invariant |distances| == n
        invariant forall j :: i + 1 <= j <= n ==> maxtaild[j] >= 0
        invariant forall j :: 0 <= j < |distances| ==> distances[j].0 >= 0 && distances[j].1 >= 0
    {
        var tmpCall1 := max(maxtaild[i + 1], distances[i].1);
        maxtaild[i] := tmpCall1;
        i := i - 1;
    }

    // Find minimum: either all covered by fountain 2, or split optimally
    var minVal := maxtaild[0];
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant minVal >= 0
        invariant |distances| == n
        invariant forall j :: 0 <= j <= n ==> maxtaild[j] >= 0
        invariant forall j :: 0 <= j < |distances| ==> distances[j].0 >= 0 && distances[j].1 >= 0
    {
        var tmpCall2 := min(minVal, distances[i].0 + maxtaild[i + 1]);
        minVal := tmpCall2;
        i := i + 1;
    }

    return minVal;
}
// </vc-code>
