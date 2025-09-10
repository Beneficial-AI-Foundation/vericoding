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
{
  if exp == 0 then 1
  else if exp == 1 then base % mod
  else
    var half := pow(base, exp / 2, mod);
    if exp % 2 == 0 then (half * half) % mod
    else (((half * half) % mod) * (base % mod)) % mod
}

lemma PowNonNegative(base: int, exp: int, mod: int)
  requires mod > 0
  requires exp >= 0
  ensures pow(base, exp, mod) >= 0
{
}

lemma PowBounded(base: int, exp: int, mod: int)
  requires mod > 0
  requires exp >= 0
  ensures 0 <= pow(base, exp, mod) < mod
{
}

lemma BlockCountFormulaBounded(n: int, i: int)
  requires n >= 1 && 1 <= i <= n
  ensures 0 <= BlockCountFormula(n, i) < MOD
{
  if i == n {
  } else {
    PowBounded(10, n - i - 1, MOD);
    if i < n - 1 {
      PowBounded(10, n - i - 2, MOD);
    }
  }
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
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant |result| == i - 1
    invariant forall k :: 0 <= k < |result| ==> 0 <= result[k] < MOD
    invariant forall k :: 0 <= k < |result| ==> 
      if k + 1 == n then result[k] == 10
      else result[k] == BlockCountFormula(n, k + 1)
  {
    if i == n {
      result := result + [10];
    } else {
      BlockCountFormulaBounded(n, i);
      var block_count := BlockCountFormula(n, i);
      result := result + [block_count];
    }
    i := i + 1;
  }
}
// </vc-code>

