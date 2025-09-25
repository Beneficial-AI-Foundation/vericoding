// <vc-preamble>
predicate ValidInput(N: int, K: int) {
  1 <= K <= N <= 2000
}

predicate ValidOutput(result: seq<int>, K: int) {
  |result| == K &&
  forall i :: 0 <= i < K ==> 0 <= result[i] < 1000000007
}

function ArrangementCount(N: int, K: int, moves: int): int
  requires ValidInput(N, K)
  requires 1 <= moves <= K
{
  if N - K < moves - 1 then 0
  else 
    var mod := 1000000007;
    var redGaps := N - K + 1;
    var blueGroups := K - 1;
    if moves - 1 > redGaps || moves - 1 > blueGroups then 0
    else 1 // Placeholder for actual combinatorial calculation
}
// </vc-preamble>

// <vc-helpers>
function Power(base: int, exp: int, mod: int): int
  requires mod > 0
  requires exp >= 0
  decreases exp
{
  if exp == 0 then 1
  else if exp % 2 == 0 then
    var half := Power(base, exp / 2, mod);
    (half * half) % mod
  else
    (base * Power(base, exp - 1, mod)) % mod
}

function ModInverse(a: int, mod: int): int
  requires mod > 1
  requires a >= 0
{
  Power(a, mod - 2, mod)
}

method ComputeFactorials(n: int, mod: int) returns (fac: array<int>, invfac: array<int>)
  requires n >= 0
  requires mod > 1
  ensures fac.Length == n + 1
  ensures invfac.Length == n + 1
  ensures fac[0] == 1
  ensures forall i :: 0 <= i <= n ==> fac[i] >= 0
  ensures forall i :: 0 <= i <= n ==> invfac[i] >= 0
{
  fac := new int[n + 1];
  invfac := new int[n + 1];

  fac[0] := 1;
  var i := 1;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant fac[0] == 1
    invariant forall j :: 0 <= j < i ==> fac[j] >= 0
  {
    fac[i] := (fac[i-1] * i) % mod;
    i := i + 1;
  }

  invfac[n] := ModInverse(fac[n], mod);
  i := n - 1;
  while i >= 0
    invariant -1 <= i <= n - 1
    invariant forall j :: 0 <= j <= n ==> fac[j] >= 0
    invariant fac[0] == 1
    invariant invfac[n] >= 0
    invariant forall j :: i < j <= n ==> invfac[j] >= 0
  {
    invfac[i] := (invfac[i+1] * (i+1)) % mod;
    i := i - 1;
  }
}

function Combination(n: int, r: int, fac: array<int>, invfac: array<int>, mod: int): int
  requires fac.Length > n >= 0
  requires invfac.Length > n >= 0
  requires 0 <= r <= n
  requires fac.Length > r
  requires invfac.Length > r
  requires mod > 0
  reads fac, invfac
{
  ((fac[n] * invfac[r]) % mod * invfac[n-r]) % mod
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, K: int) returns (result: seq<int>)
  requires ValidInput(N, K)
  ensures ValidOutput(result, K)
  ensures forall i :: 0 <= i < K ==> (N - K < i ==> result[i] == 0)
// </vc-spec>
// <vc-code>
{
  var mod := 1000000007;
  var fac, invfac := ComputeFactorials(N, mod);

  result := [];
  var i := 0;
  while i < K
    invariant 0 <= i <= K
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> 0 <= result[j] < mod
    invariant forall j :: 0 <= j < i ==> (N - K < j ==> result[j] == 0)
    invariant forall j :: 0 <= j < i ==> (N - K >= j ==> result[j] == (Combination(N - K + 1, j + 1, fac, invfac, mod) * Combination(K - 1, j, fac, invfac, mod)) % mod)
  {
    if N - K < i {
      result := result + [0];
    } else {
      var tmpCall1 := Combination(N - K + 1, i + 1, fac, invfac, mod);
      var tmp1 := tmpCall1;
      var tmp2 := Combination(K - 1, i, fac, invfac, mod);
      var answer := (tmp1 * tmp2) % mod;
      result := result + [answer];
    }
    i := i + 1;
  }
}
// </vc-code>
