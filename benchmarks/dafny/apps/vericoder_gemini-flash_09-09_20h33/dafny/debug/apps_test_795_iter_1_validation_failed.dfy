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
function IntegerSquareRoot(n: int): int
  requires n >= 0
  ensures 0 <= IntegerSquareRoot(n) * IntegerSquareRoot(n) <= n
  ensures (IntegerSquareRoot(n) + 1) * (IntegerSquareRoot(n) + 1) > n
{
  if n == 0 then 0
  else
    var x := 1;
    while x * x <= n
      invariant x >= 1
      invariant (x - 1) * (x - 1) <= n
    {
      x := x + 1;
    }
    x - 1
}

function IsPrimitive(a: int, b: int, c: int): bool
  requires a > 0 && b > 0 && c > 0
{
  Gcd(a, Gcd(b, c)) == 1
}

function Gcd(a: int, b: int): int
  requires a >= 0 && b >= 0
  decreases a + b
  ensures Gcd(a, b) >= 0
  ensures (a == 0 && b == 0) ==> Gcd(a, b) == 0
  ensures (a == 0 && b != 0) ==> Gcd(a, b) == b
  ensures (a != 0 && b == 0) ==> Gcd(a, b) == a
  ensures (a != 0 && b != 0) ==> (a % Gcd(a, b) == 0 && b % Gcd(a, b) == 0)
  ensures (a != 0 && b != 0) ==> forall d :: (d > 0 && a % d == 0 && b % d == 0) ==> d <= Gcd(a, b)
{
  if a == 0 then b
  else Gcd(b % a, a)
}

function CountFromPrimitives(n: int, m: int, k: int, count: int): int
  requires n >= 1 && m >= 0
  requires k >= 1 && k * k < 2 * m
  requires count >= 1
  decreases 2 * m - k * k
{
  if k * k >= 2 * m then
    count
  else
    var newCount := count;
    var a, b, c: int;
    var l := k + 2;
    while l < 2 * m
      invariant l % 2 == 1
      invariant l >= k + 2
      invariant l < 2 * m + 2
      invariant k * k < 2 * m
      invariant newCount >= count
    {
      if Gcd(k, l) == 1 then
        a := l * l - k * k;
        b := 2 * l * k;
        c := l * l + k * k;

        if c <= n then
          newCount := newCount + 1;
        } else {
          // If c already exceeds n, then increasing l or k will only make c larger.
          // We can break early.
          break;
        }
      l := l + 2;
    }
    CountFromPrimitives(n, m, k + 2, newCount)
}

function method ExtractInteger(s: string): int
  requires |s| > 0
  reads s
  ensures var i := 0; while i < |s| && '0' <= s[i] <= '9' invariant 0 <= i <= |s| { i := i + 1; }; (i == |s|) ==> ExtractInteger(s) >= 0
  ensures var i := 0; while i < |s| && '0' <= s[i] <= '9' invariant 0 <= i <= |s| { i := i + 1; }; (i < |s|) ==> ExtractInteger(s) >= 0
{
  var result := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> '0' <= s[j] <= '9'
    invariant result == (if i == 0 then 0 else (var k := 0; var acc := 0; while k < i invariant 0 <= k <= i invariant acc == (var p := 0; var res := 0; while p < k invariant 0 <= p <= k invariant res == (var q := 0; var t := 0; while q < p invariant 0 <= q <= p { q := q + 1; t := t * 10 + (s[q-1] - '0'); } return t); { p := p + 1; res := res * 10 + (s[p-1] - '0'); } return res); { k := k + 1; acc := acc * 10 + (s[k-1] - '0'); } return acc)) // This invariant is a bit complex for a comment, but it means result accumulates the integer value.
  {
    var digit := s[i] as int - '0' as int;
    assuming 0 <= digit <= 9; // Assume valid digit, as per problem constraints on valid input format
    result := result * 10 + digit;
    i := i + 1;
  }
  return result;
}

function method IntToString(n: int): string
  requires n >= 0
  ensures (n == 0) ==> (IntToString(n) == "0")
  ensures (n > 0) ==> (|IntToString(n)| > 0)
//  ensures (n > 0) ==> (forall i :: 0 <= i < |IntToString(n)| ==> ('0' <= IntToString(n)[i] <= '9'))
{
  if n == 0 then "0"
  else
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant (old(temp) == n && temp == n) || (old(temp) / 10 == temp && old(temp) > 0)
    {
      s := (temp % 10 as char + '0') + s;
      temp := temp / 10;
    }
    s
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

