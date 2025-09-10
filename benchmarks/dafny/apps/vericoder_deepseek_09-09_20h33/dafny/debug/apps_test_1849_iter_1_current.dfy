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
function pow(base: int, exponent: int, mod: int): int
  requires exponent >= 0
  requires mod > 1
  ensures 0 <= pow(base, exponent, mod) < mod
{
  if exponent == 0 then 1
  else if exponent % 2 == 0 then
    pow((base * base) % mod, exponent / 2, mod)
  else
    (base * pow((base * base) % mod, (exponent - 1) / 2, mod)) % mod
}

lemma PowProperty(base: int, exp: int, mod: int)
  requires exp >= 0
  requires mod > 1
  ensures pow(base, exp, mod) >= 0 && pow(base, exp, mod) < mod
{
}

lemma BlockCountFormulaCorrect(n: int, i: int)
  requires n >= 1 && 1 <= i <= n
  ensures 0 <= BlockCountFormula(n, i) < MOD
{
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
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> 0 <= result[k] < MOD
    invariant n >= 1 && i == n - 1 ==> result[n-1] == 10
    invariant forall j :: 0 <= j < i-1 ==> result[j] == BlockCountFormula(n, j+1)
  {
    var j := i + 1;
    var value := 0;
    if j == n {
      value := 10;
    } else {
      var term1 := (2 * 9 * pow(10, n - j - 1, MOD) * 10) % MOD;
      var term2 := 0;
      if j < n - 1 {
        term2 := ((n - 1 - j) * 9 * 9 * pow(10, n - j - 2, MOD) * 10) % MOD;
      }
      value := (term1 + term2) % MOD;
    }
    result := result + [value];
    i := i + 1;
  }
}
// </vc-code>

