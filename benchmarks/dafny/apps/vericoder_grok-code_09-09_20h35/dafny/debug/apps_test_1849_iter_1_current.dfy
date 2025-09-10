const MOD := 998244353

predicate ValidInput(n: int)
{
  n >= 1
}

function BlockCountFormula(n: int, i: int): int
  requires n >= 1 && 1 <= i <= n
{
  if i == n then 10
  else 
    ((2 * 9 * pow(10, n - i - 1, MOD) * 10) + 
     (if i < n - 1 then ((n - 1 - i) * 9 * 9 * pow(10, n - i - 2, MOD) * 10) else 0)) % MOD
}

predicate ValidResult(result: seq<int>, n: int)
  requires n >= 1
{
  |result| == n &&
  (forall k :: 0 <= k < n ==> 0 <= result[k] < MOD) &&
  (n >= 1 ==> result[n-1] == 10) &&
  (forall i :: 0 <= i < n-1 ==> result[i] == BlockCountFormula(n, i+1))
}

// <vc-helpers>
function pow(base: int, exp: nat, m: int): int
  requires m > 0
  decreases exp
{
  if exp == 0 then 1
  else if exp % 2 == 0 then pow((base * base) % m, exp / 2, m) % m
  else (base * pow(base, exp - 1, m) % m) % m
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<int>)
  requires ValidInput(n)
  ensures ValidResult(result, n)
// </vc-spec>
// <vc-code>
var result: seq<int> := [];
var i := 1;
while i < n
  invariant 1 <= i <= n
  invariant |result| == i - 1
  invariant forall k :: 0 <= k < |result| ==> result[k] == BlockCountFormula(n, k + 1)
{
  result := result + [BlockCountFormula(n, i)];
  i := i + 1;
}
result := result + [10];
// </vc-code>

