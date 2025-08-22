//IMPL 
method RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
{
    if |l| == 0 {
        r := [];
    } else {
        var effectiveN := n % |l|;
        r := l[|l| - effectiveN..] + l[..|l| - effectiveN];
    }
}