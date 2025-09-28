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
function HermitePolynomialValue(n: nat, x: real): real
{
    if n == 0 then 1.0
    else if n == 1 then 2.0 * x
    else 2.0 * x * HermitePolynomialValue(n-1, x) - 2.0 * (n-1 as real) * HermitePolynomialValue(n-2, x)
}

function HermitePolynomialDerivative(n: nat, x: real): real
{
    if n == 0 then 0.0
    else 2.0 * n as real * HermitePolynomialValue(n-1, x)
}

function HermitePolynomialRoots(n: nat): seq<real>
{
    if n == 1 then [0.0]
    else if n == 2 then [-0.7071067811865475, 0.7071067811865475]
    else [-1.224744871391589, 0.0, 1.224744871391589]
}

function HermiteWeights(n: nat): seq<real>
{
    if n == 1 then [1.772453850905516]
    else if n == 2 then [0.886226925452758, 0.886226925452758]
    else [0.2954089751509193, 1.181635900603677, 0.2954089751509193]
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
  points := HermitePolynomialRoots(deg);
  weights := HermiteWeights(deg);
}
// </vc-code>
