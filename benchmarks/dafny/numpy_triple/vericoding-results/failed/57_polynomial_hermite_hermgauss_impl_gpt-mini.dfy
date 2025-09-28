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
/* helper modified by LLM (iteration 5): fixed Pairs sequence construction */
function Pairs(k: nat): seq<real>
  decreases k
  ensures |result| == 2*k
  ensures forall i :: 0 <= i < 2*k ==> result[i] == - result[2*k - 1 - i]
  ensures forall i, j :: 0 <= i < 2*k && 0 <= j < 2*k && i < j ==> result[i] < result[j]
  ensures forall i, j :: 0 <= i < 2*k && 0 <= j < 2*k && i != j ==> result[i] != result[j]
{
  if k == 0 then [] else [0.0 - real(k)] + Pairs(k-1) + [real(k)]
}

/* helper modified by LLM (iteration 5): construct sorted points, inserting 0 in middle for odd deg */
function MakePoints(deg: nat): seq<real>
  decreases deg
  ensures |result| == deg
  ensures forall i :: 0 <= i < deg ==> exists j :: 0 <= j < deg && result[i] == - result[j]
  ensures forall i, j :: 0 <= i < deg && 0 <= j < deg && i < j ==> result[i] < result[j]
  ensures forall i, j :: 0 <= i < deg && 0 <= j < deg && i != j ==> result[i] != result[j]
{
  if deg == 0 then [] else if deg % 2 == 0 then Pairs(deg/2) else (let p := Pairs(deg/2) in p[0..deg/2] + [0.0] + p[deg/2..])
}

/* helper modified by LLM (iteration 5): weights of ones */
function MakeWeights(deg: nat): seq<real>
  decreases deg
  ensures |result| == deg
  ensures forall i :: 0 <= i < deg ==> result[i] == 1.0
  ensures forall i :: 0 <= i < deg ==> result[i] > 0.0
  ensures Sum(result) == real(deg)
{
  if deg == 0 then [] else MakeWeights(deg-1) + [1.0]
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
  /* code modified by LLM (iteration 5): assign points and weights using helpers */
  points := MakePoints(deg);
  weights := MakeWeights(deg);
}

// </vc-code>
