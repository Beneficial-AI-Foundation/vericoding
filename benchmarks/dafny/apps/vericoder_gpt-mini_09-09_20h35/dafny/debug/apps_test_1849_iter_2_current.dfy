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
  requires e >= 0 && m > 0
  decreases e
{
  if e == 0 then 1 % m else ((b % m) * pow(b, e - 1, m)) % m
}

lemma ModNonnegRange(x: int, m: int)
  requires m > 0 && x >= 0
  ensures 0 <= x % m < m
{
  // Dafny can prove the standard modulus bounds for non-negative x
  assert 0 <= x % m;
  assert x % m < m;
}

lemma PowRange(b: int, e: int, m: int)
  requires e >= 0 && m > 0
  ensures 0 <= pow(b, e, m) < m
  decreases e
{
  if e == 0 {
    // pow(b,0,m) == 1 % m
    assert pow(b, 0, m) == 1 % m;
    ModNonnegRange(1, m);
    assert 0 <= pow(b, 0, m) < m;
  } else {
    // pow(b,e,m) == ((b % m) * pow(b,e-1,m)) % m
    PowRange(b, e - 1, m);
    var t := pow(b, e - 1, m);
    assert 0 <= t < m;
    var prod := (b % m) * t;
    assert prod >= 0;
    ModNonnegRange(prod, m);
    assert pow(b, e, m) == prod % m;
    assert 0 <= pow(b, e, m) < m;
  }
}

lemma BlockCountFormula_range(n: int, i: int)
  requires n >= 1 && 1 <= i <= n
  ensures 0 <= BlockCountFormula(n, i) < MOD
{
  if i == n {
    assert BlockCountFormula(n, i) == 10;
    assert 0 <= 10 < MOD;
  } else {
    // Expand the function body to show the inner argument to % is non-negative
    if i < n - 1 {
      var p1 := pow(10, n - i - 1, MOD);
      PowRange(10, n - i - 1, MOD);
      assert 0 <= p1 < MOD;
      var term1 := 2 * 9 * p1 * 10;
      assert term1 >= 0;
      var p2 := pow(10, n - i - 2, MOD);
      PowRange(10, n - i - 2, MOD);
      assert 0 <= p2 < MOD;
      var term2 := (n - 1 - i) * 9 * 9 * p2 * 10;
      assert term2 >= 0;
      var sum := term1 + term2;
      assert sum >= 0;
      ModNonnegRange(sum, MOD);
      assert BlockCountFormula(n, i) == sum % MOD;
      assert 0 <= BlockCountFormula(n, i) < MOD;
    } else {
      // i == n-1 case (but still i != n)
      var p := pow(10, n - i - 1, MOD);
      PowRange(10, n - i - 1, MOD);
      assert 0 <= p < MOD;
      var sum := 2 * 9 * p * 10;
      assert sum >= 0;
      ModNonnegRange(sum, MOD);
      assert BlockCountFormula(n, i) == sum % MOD;
      assert 0 <= BlockCountFormula(n, i) < MOD;
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
  var arr := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> arr[j] == BlockCountFormula(n, j+1)
    invariant forall j :: 0 <= j < i ==> 0 <= arr[j] < MOD
    decreases n - i
  {
    arr[i] := BlockCountFormula(n, i + 1);
    // help the verifier by proving the assigned value is in range
    call BlockCountFormula_range(n, i + 1);
    assert 0 <= arr[i] < MOD;
    assert arr[i] == BlockCountFormula(n, i + 1);
    i := i + 1;
  }
  return arr[..];
}
// </vc-code>

