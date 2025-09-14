predicate ValidInput(N: int, D: int)
{
  N >= 1 && N <= 20 && D >= 1 && D <= 20
}

function CoverageRange(position: int, D: int): (int, int)
{
  (position - D, position + D)
}

predicate TreesCovered(N: int, D: int, inspectors: int)
{
  inspectors >= 1 && inspectors <= N && inspectors == ((N - 1) / (2 * D + 1)) + 1
}

// <vc-helpers>
lemma DivLe(x: nat, y: int)
    requires y > 1
    ensures x / y <= x
{
    var q := x / y;
    if q > x {
        var r := x % y;
        assert x == q * y + r;
        calc {
            x;
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
lemma DivLe(x: nat, y: int)
    requires y > 1
    ensures x / y <= x
{
    var q := x / y;
    if q > x {
        var r := x % y;
        assert x == q * y + r;
        calc {
            x;
// </vc-code>

