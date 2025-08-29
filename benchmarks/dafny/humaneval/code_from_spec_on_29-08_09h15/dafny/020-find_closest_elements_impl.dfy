function dist(a: real, b: real) : (d : real)
    ensures d >= 0.0
    ensures (d == 0.0) <==> a == b
{
    if a < b then b - a else a - b
}
function des(s: seq<real>, a: int, b: int) : bool {
    // distinct elements
    0 <= a < |s| && 0 <= b < |s| && a != b
}

// <vc-helpers>
lemma DistCommutative(a: real, b: real)
    ensures dist(a, b) == dist(b, a)
{
}

lemma DistTriangleInequality(a: real, b: real, c: real)
    ensures dist(a, c) <= dist(a, b) + dist(b, c)
{
}

lemma MinDistanceExists(s: seq<real>)
    requires |s| >= 2
    ensures exists a, b : int :: des(s, a, b) && 
            (forall c, d : int :: des(s, c, d) ==> dist(s[a], s[b]) <= dist(s[c], s[d]))
{
    assert des(s, 0, 1);
    var minA, minB := 0, 1;
    var minDist := dist(s[0], s[1]);
    
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant des(s, minA, minB)
        invariant forall a, b : int :: des(s, a, b) && (a < i || (a == i && b <= i)) ==> minDist <= dist(s[a], s[b])
        invariant minDist == dist(s[minA], s[minB])
    {
        var j := i + 1;
        while j < |s|
            invariant i + 1 <= j <= |s|
            invariant des(s, minA, minB)
            invariant forall a, b : int :: des(s, a, b) && (a < i || (a == i && b < j)) ==> minDist <= dist(s[a], s[b])
            invariant minDist == dist(s[minA], s[minB])
        {
            if dist(s[i], s[j]) < minDist {
                minDist := dist(s[i], s[j]);
                minA := i;
                minB := j;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    assert forall c, d : int :: des(s, c, d) ==> dist(s[minA], s[minB]) <= dist(s[c], s[d]);
}

function FindMin(s: set<real>): real
    requires s != {}
    ensures FindMin(s) in s
    ensures forall x :: x in s ==> FindMin(s) <= x
{
    var x :| x in s && forall y :: y in s ==> x <= y;
    x
}

lemma FindMinProperties(s: set<real>)
    requires s != {}
    ensures FindMin(s) in s
    ensures forall x :: x in s ==> FindMin(s) <= x
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def find_closest_elements(numbers: List[float]) -> Tuple[float, float]
From a supplied list of numbers (of length at least two) select and return two that are the closest to each other and return them in order (smaller number, larger number).
*/
// </vc-description>

// <vc-spec>
method find_closest_elements(s: seq<real>) returns (l : real, h : real)
    // pre-conditions-start
    requires |s| >= 2
    // pre-conditions-end
    // post-conditions-start
    ensures exists a, b : int :: des(s, a, b) && l == s[a] && h == s[b]
    ensures forall a, b : int :: des(s, a, b) ==> dist(l, h) <= dist(s[a], s[b])
    ensures l <= h
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    var minDist := dist(s[0], s[1]);
    var bestA, bestB := 0, 1;
    
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant des(s, bestA, bestB)
        invariant forall a, b : int :: des(s, a, b) && (a < i || (a == i && b <= i)) ==> minDist <= dist(s[a], s[b])
        invariant minDist == dist(s[bestA], s[bestB])
    {
        var j := i + 1;
        while j < |s|
            invariant i + 1 <= j <= |s|
            invariant des(s, bestA, bestB)
            invariant forall a, b : int :: des(s, a, b) && (a < i || (a == i && b < j)) ==> minDist <= dist(s[a], s[b])
            invariant minDist == dist(s[bestA], s[bestB])
        {
            if dist(s[i], s[j]) < minDist {
                minDist := dist(s[i], s[j]);
                bestA := i;
                bestB := j;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    assert forall a, b : int :: des(s, a, b) ==> minDist <= dist(s[a], s[b]);
    assert forall a, b : int :: des(s, a, b) ==> dist(s[bestA], s[bestB]) <= dist(s[a], s[b]);
    
    if s[bestA] <= s[bestB] {
        l := s[bestA];
        h := s[bestB];
    } else {
        l := s[bestB];
        h := s[bestA];
    }
}
// </vc-code>

