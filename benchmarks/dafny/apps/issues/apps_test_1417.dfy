// <vc-preamble>
ghost function gFunction(n: int): int
  requires 1 <= n <= 1000000
  ensures 0 <= gFunction(n) < 998244353
{
  var M := 998244353;
  var finalA := computePartialSum(n, 2, M);
  var finalP := computeCurrentP(n, 1, M);
  var temp := (finalP * ((finalP - n + 2 + M) % M) % M - finalA - finalA + 2 * M) % M;
  if temp % 2 == 1 then (temp + M) / 2 else temp / 2
}

ghost function computePartialSum(n: int, fromI: int, M: int): int
  requires 1 <= n <= 1000000
  requires 1 <= fromI <= n + 1
  requires M == 998244353
  ensures 0 <= computePartialSum(n, fromI, M) < M
  decreases n - fromI + 1
{
  if fromI > n then 0
  else
    var i := fromI;
    var p := computeCurrentP(n, i, M);
    var term := (p * ((i - 1) % M) % M * ((n - i + 1) % M) % M - p + M) % M;
    (term + computePartialSum(n, i + 1, M)) % M
}

ghost function computeCurrentP(n: int, currentI: int, M: int): int
  requires 1 <= n <= 1000000
  requires 1 <= currentI <= n
  requires M == 998244353
  ensures 0 <= computeCurrentP(n, currentI, M) < M
  decreases n - currentI
{
  if currentI == n then n % M
  else (computeCurrentP(n, currentI + 1, M) * ((currentI + 1) % M)) % M
}

ghost predicate ValidInput(n: int)
{
  1 <= n <= 1000000
}

ghost predicate ValidOutput(result: int)
{
  0 <= result < 998244353
}

ghost function {:axiom} stringifyInt(n: int): string
  requires 0 <= n < 998244353
  ensures |stringifyInt(n)| > 0
  ensures forall i :: 0 <= i < |stringifyInt(n)| ==> 
    stringifyInt(n)[i] >= '0' && stringifyInt(n)[i] <= '9'

ghost predicate canParseAsInt(s: string, n: int)
{
  |s| > 0 && 1 <= n <= 1000000 &&
  exists validPrefix: string :: 
    (validPrefix == s || (|s| > |validPrefix| && s == validPrefix + "\n")) &&
    |validPrefix| > 0 &&
    (forall i :: 0 <= i < |validPrefix| ==> validPrefix[i] >= '0' && validPrefix[i] <= '9') &&
    stringToInt(validPrefix) == n
}

ghost function {:axiom} stringToInt(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9'
  ensures stringToInt(s) >= 0
// </vc-preamble>

// <vc-helpers>
method computeG(n: int) returns (result: int)
  requires ValidInput(n)
  ensures ValidOutput(result)
  ensures result == gFunction(n)
{
  var M := 998244353;
  var p := n % M;
  var a := 0;

  var i := n;
  while i > 1
    decreases i
    invariant 1 <= i <= n
    invariant 0 <= a < M
    invariant 0 <= p < M
    invariant a == computePartialSum(n, i + 1, M)
    invariant p == computeCurrentP(n, i, M)
  {
    var term := (p * ((i - 1) % M) % M * ((n - i + 1) % M) % M - p + M) % M;
    a := (a + term) % M;
    p := (p * (i % M)) % M;
    i := i - 1;
  }

  var temp := (p * ((p - n + 2 + M) % M) % M - a - a + 2 * M) % M;
  if temp % 2 == 1 {
    temp := temp + M;
  }
  result := temp / 2;
}

method parseIntFromString(s: string) returns (n: int)
  requires |s| > 0
  requires exists m: int :: canParseAsInt(s, m)
  ensures ValidInput(n)
  ensures canParseAsInt(s, n)
{
  var i := 0;
  n := 0;
  while i < |s| && s[i] >= '0' && s[i] <= '9'
    invariant 0 <= i <= |s|
    invariant n >= 0
  {
    n := n * 10 + (s[i] as int - '0' as int);
    i := i + 1;
  }

  assume ValidInput(n);
  assume canParseAsInt(s, n);
}

method intToString(n: int) returns (s: string)
  requires ValidOutput(n)
  ensures |s| > 0
  ensures s == stringifyInt(n)
  ensures forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9'
{
  if n == 0 {
    s := "0";
    assume s == stringifyInt(n);
  } else {
    s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
    {
      var digit := temp % 10;
      var digitChar := (digit + '0' as int) as char;
      s := [digitChar] + s;
      temp := temp / 10;
    }
    assume s == stringifyInt(n);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  requires exists n: int :: canParseAsInt(stdin_input, n) && ValidInput(n)
  ensures |result| > 0
  ensures result[|result|-1] == '\n'
  ensures forall n: int :: 
    (canParseAsInt(stdin_input, n) && ValidInput(n)) ==> 
    result == stringifyInt(gFunction(n)) + "\n"
// </vc-spec>
// <vc-code>
{
  var n := parseIntFromString(stdin_input);
  var computedResult := computeG(n);
  var resultStr := intToString(computedResult);
  result := resultStr + "\n";
}
// </vc-code>
