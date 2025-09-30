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
function pow(base: int, exp: int, mod: int): int
  requires mod > 0
  requires exp >= 0
  decreases exp
{
  if exp == 0 then 1
  else (base * pow(base, exp - 1, mod)) % mod
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<int>)
  requires ValidInput(n)
  ensures ValidResult(result, n)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> 0 <= result[k] < MOD
    invariant i >= 1 && i <= n ==> result[i-1] == (if i == n then 10 else BlockCountFormula(n, i))
    invariant forall j :: 0 <= j < i && j < n-1 ==> result[j] == BlockCountFormula(n, j+1)
  {
    var val: int;
    if i == n - 1 {
      val := 10;
    } else {
      val := BlockCountFormula(n, i + 1);
    }
    result := result + [val];
    i := i + 1;
  }
}
// </vc-code>

