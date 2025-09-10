predicate ValidInput(input: string)
{
  |input| > 0
}

predicate ValidN(n: int)
{
  n >= 1 && n <= 10000
}

function CountPythagoreanTriplesViaPrimitives(n: int): int
  requires ValidN(n)
{
  var m := IntegerSquareRoot(n);
  CountFromPrimitives(n, m, 1, 1)
}

// <vc-helpers>
function CountFromPrimitives(n: int, m: int, k: int, count: int): int
  requires n >= 1 && m >= 1
  decreases m, k
{
  if m * m * 2 > n then
    count
  else if k * k * 2 > n then
    CountFromPrimitives(n, m + 1, m + 2, count)
  else if (m * m + k * k) * (m * m + k * k) <= n then // Check if the triple fits within n
  (
    if Gcd(m, k) == 1 then
      CountTriplesForPrimitive(n, m, k, count)
    else
      CountFromPrimitives(n, m, k + 2, count)
  )
  else
    CountFromPrimitives(n, m, k + 2, count)
}

function CountTriplesForPrimitive(n: int, m: int, k: int, count: int): int
  requires n >= 1 && m >= 1 && k >= 1 && m > k
  requires Gcd(m,k) == 1
  decreases n, count
{
  var a := m * m - k * k;
  var b := 2 * m * k;
  var c := m * m + k * k;
  if n >= c then
    CountTriplesForPrimitive(n, m, k, count + 1)
  else
    count
}

function Gcd(a: nat, b: nat): nat
  decreases a, b
{
  if b == 0 then a else Gcd(b, a % b)
}

function IntegerSquareRoot(n: nat): nat
  ensures (result * result <= n) && ((result + 1) * (result + 1) > n)
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else
    var low := 0;
    var high := n;
    var ans := 0;
    while low <= high
      invariant 0 <= low <= high + 1
      invariant ans * ans <= n
      invariant (ans+1)*(ans+1) > n ==> ans >= low
      invariant high >= low -1
      decreases high - low
    {
      var mid := low + (high - low) / 2;
      if mid * mid <= n
      {
        ans := mid;
        low := mid + 1;
      }
      else
      {
        high := mid - 1;
      }
    }
    ans
}

function ExtractInteger(s: string): int
  requires |s| > 0
  reads s
  ensures forall i :: 0 <= i < |s| :: '0' <= s[i] <= '9' ==> result >= 0
  ensures forall i :: 0 <= i < |s| :: !('0' <= s[i] <= '9') ==> result == 0
  ensures varR: result >= 0
{
  var res := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant res >= 0
  {
    if '0' <= s[i] <= '9'
    {
      res := res * 10 + (s[i] as int - '0' as int);
    }
    else
    {
      return 0; // Or handle error appropriately
    }
    i := i + 1;
  }
  return res;
}

function IntToString(n: int): string
  requires n >= 0
  ensures var_len: |result| > 0
  ensures var_val: (if n == 0 then result == "0" else (var x := n; var s_rev := ""; while x > 0 { s_rev := s_rev + (('0' as int + x % 10) as char); x := x / 10; } (var res_rev := ""; for k := 0 to |s_rev|-1 { res_rev := res_rev + s_rev[|s_rev|-1-k]; } result == res_rev)))
{
  if n == 0 then "0"
  else
  {
    var s_rev := "";
    var x := n;
    while x > 0
      invariant x >= 0
      invariant (x == 0 && s_rev == "") || (x > 0 && |s_rev| > 0) || (x == n && s_rev == "")
    {
      s_rev := s_rev + ((x % 10 as char) + '0');
      x := x / 10;
    }
    var res_rev := "";
    for k := 0 to |s_rev|-1
      invariant 0 <= k <= |s_rev|
      invariant |res_rev| == k
    {
      res_rev := res_rev + s_rev[|s_rev|-1-k];
    }
    res_rev
  }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires ValidInput(stdin_input)
  ensures |result| > 0
  ensures result == IntToString(CountPythagoreanTriplesViaPrimitives(ExtractInteger(stdin_input)))
// </vc-spec>
// <vc-code>
{
  var n := ExtractInteger(stdin_input);
  var count := CountPythagoreanTriplesViaPrimitives(n);
  result := IntToString(count);
}
// </vc-code>

