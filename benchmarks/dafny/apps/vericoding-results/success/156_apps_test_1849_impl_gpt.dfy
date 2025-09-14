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
function pow(b: int, e: int, m: int): int
  requires m > 0
  requires e >= 0
  decreases e
  ensures 0 <= pow(b, e, m) < m
{
  if e == 0 then 1 % m
  else (b % m * pow(b, e - 1, m)) % m
}

lemma BlockCountFormulaRangeLemma(n: int, i: int)
  requires n >= 1 && 1 <= i <= n
  ensures 0 <= BlockCountFormula(n, i) < MOD
{
  assert 0 < MOD;
  if i == n {
    assert BlockCountFormula(n, i) == 10;
    assert 0 <= BlockCountFormula(n, i) < MOD;
  } else {
    var e := (2 * 9 * pow(10, n - i - 1, MOD) * 10) +
             (if i < n - 1 then ((n - 1 - i) * 9 * 9 * pow(10, n - i - 2, MOD) * 10) else 0);
    assert BlockCountFormula(n, i) == e % MOD;
    assert 0 <= e % MOD < MOD;
    assert 0 <= BlockCountFormula(n, i) < MOD;
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
  var res: seq<int> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==> res[k] == BlockCountFormula(n, k + 1)
    invariant forall k :: 0 <= k < i ==> 0 <= res[k] < MOD
    decreases n - i
  {
    BlockCountFormulaRangeLemma(n, i + 1);
    res := res + [BlockCountFormula(n, i + 1)];
    i := i + 1;
  }
  result := res;
}
// </vc-code>

