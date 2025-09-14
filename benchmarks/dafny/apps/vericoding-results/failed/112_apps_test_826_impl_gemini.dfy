predicate ValidInput(n: int)
{
  n >= 1
}

predicate IsOptimalSavings(n: int, savings: int)
  requires n >= 1
{
  savings >= 0 &&
  (2 + savings) * (savings + 1) / 2 > n + 1 &&
  (savings == 0 || (2 + (savings - 1)) * savings / 2 <= n + 1)
}

predicate IsMinimalSavings(n: int, savings: int)
  requires n >= 1
{
  IsOptimalSavings(n, savings) &&
  (forall j :: j >= 0 && j < savings ==> (2 + j) * (j + 1) / 2 <= n + 1)
}

function OptimalCost(n: int, savings: int): int
  requires n >= 1
  requires IsOptimalSavings(n, savings)
{
  n - savings + 1
}

// <vc-helpers>
lemma BoundedSavings(n: int, savings: int)
  requires n >= 1
  requires savings >= 1
  requires (savings * (savings + 1)) / 2 <= n + 1
  ensures savings <= n
{
  if savings > n {
    assert savings >= n + 1;
    var v1 := (savings * (savings + 1));
    var v2 := 2 * (n + 1);
    assert v1 <= v2; // from the requires clause

    var lhs := (n + 1) * ((n + 1) + 1);
    assert v1 >= lhs; // Since f(x)=x(x+1) is increasing for x>=1

    var rhs := 2 * (n + 1);
    assert lhs > rhs; // (n+1)(n+2) > 2(n+1
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires ValidInput(n)
  ensures result >= 1
  ensures result <= n
  ensures exists savings :: IsMinimalSavings(n, savings) && result == OptimalCost(n, savings)
// </vc-spec>
// <vc-code>
lemma BoundedSavings(n: int, savings: int)
  requires n >= 1
  requires savings >= 1
  requires (savings * (savings + 1)) / 2 <= n + 1
  ensures savings <= n
{
  if savings > n {
    assert savings >= n + 1;
    var v1 := (savings * (savings + 1));
    var v2 := 2 * (n + 1);
    assert v1 <= v2; // from the requires clause

    var lhs := (n + 1) * ((n + 1) + 1);
    assert v1 >= lhs; // Since f(x)=x(x+1) is increasing for x>=1

    var rhs := 2 * (n + 1);
    assert lhs > rhs; // (n+1)(n+2) > 2(n+1
// </vc-code>

