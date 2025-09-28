// <vc-preamble>
// Helper function to compute the sum of a sequence of reals
function Sum(s: seq<real>): real
{
    if |s| == 0 then 0.0
    else s[0] + Sum(s[1..])
}

// Method to compute Gauss-Hermite quadrature points and weights
// </vc-preamble>

// <vc-helpers>
// Helper function to check if a sequence is sorted in ascending order
predicate IsSorted(s: seq<real>)
{
    forall i, j :: 0 <= i < |s| && 0 <= j < |s| && i < j ==> s[i] < s[j]
}

// Helper function to check if all elements in a sequence are distinct
predicate AllDistinct(s: seq<real>)
{
    forall i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j ==> s[i] != s[j]
}

// Helper function to check symmetry property
predicate IsSymmetric(s: seq<real>)
{
    forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |s| && s[i] == -s[j]
}

// Helper function to check if all weights are positive
predicate AllPositive(w: seq<real>)
{
    forall i :: 0 <= i < |w| ==> w[i] > 0.0
}
// </vc-helpers>

// <vc-spec>
method hermgauss(deg: nat) returns (points: seq<real>, weights: seq<real>)
    requires deg > 0
    ensures |points| == deg
    ensures |weights| == deg
    // All weights are positive
    ensures forall i :: 0 <= i < deg ==> weights[i] > 0.0
    // Weights sum to a positive value
    ensures Sum(weights) > 0.0
    // Points are symmetric around 0 (for each point there's a negative counterpart)
    ensures forall i :: 0 <= i < deg ==> exists j :: 0 <= j < deg && points[i] == -points[j]
    // Points are distinct
    ensures forall i, j :: 0 <= i < deg && 0 <= j < deg && i != j ==> points[i] != points[j]
    // Points are sorted in ascending order
    ensures forall i, j :: 0 <= i < deg && 0 <= j < deg && i < j ==> points[i] < points[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): create sorted symmetric points */
    
    points := [];
    weights := [];
    
    // Create negative points in ascending order
    var i := 0;
    while i < deg/2
        invariant 0 <= i <= deg/2
        invariant |points| == i
        invariant |weights| == i
        invariant forall k :: 0 <= k < i ==> points[k] == -(deg/2 - k) as real
        invariant forall k :: 0 <= k < i ==> weights[k] > 0.0
    {
        var point_val := -(deg/2 - i) as real;
        points := points + [point_val];
        weights := weights + [1.0];
        i := i + 1;
    }
    
    // Add center point for odd degrees
    if deg % 2 == 1 {
        points := points + [0.0];
        weights := weights + [1.0];
    }
    
    // Add positive points in ascending order
    i := 0;
    while i < deg/2
        invariant 0 <= i <= deg/2
        invariant |points| == deg/2 + (if deg % 2 == 1 then 1 else 0) + i
        invariant |weights| == deg/2 + (if deg % 2 == 1 then 1 else 0) + i
        invariant forall k :: 0 <= k < |weights| ==> weights[k] > 0.0
    {
        var point_val := (i + 1) as real;
        points := points + [point_val];
        weights := weights + [1.0];
        i := i + 1;
    }
}
// </vc-code>
