// <vc-preamble>
function isPrimeResult(k: int): bool
  requires k >= 2
{
  forall d :: 2 <= d < k ==> k % d != 0
}

predicate ValidInput(input: string)
{
  forall c :: c in input ==> c in "0123456789\n\r " &&
  exists trimmed :: trimmed == TrimString(input) && |trimmed| > 0
}

function TrimString(s: string): string
{
  if |s| == 0 then s
  else if s[|s|-1] == '\n' || s[|s|-1] == ' ' || s[|s|-1] == '\r' then TrimString(s[..|s|-1])
  else s
}

function StringToInt(s: string): int
{
  var trimmed := TrimString(s);
  if |trimmed| == 0 then 0
  else if trimmed[0] == '-' then -StringToIntHelper(trimmed[1..])
  else StringToIntHelper(trimmed)
}

function StringToIntHelper(s: string): int
{
  if |s| == 0 then 0
  else if |s| == 1 then (s[0] as int - '0' as int)
  else StringToIntHelper(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}
// </vc-preamble>

// <vc-helpers>
method isPrime(k: int) returns (result: bool)
  requires k >= 2
  ensures result <==> isPrimeResult(k)
{
  var i := 2;
  while i * i <= k 
    invariant 2 <= i
    invariant forall d :: 2 <= d < i ==> k % d != 0
  {
    if k % i == 0 {
      return false;
    }
    i := i + 1;
  }

  assert forall d :: 2 <= d < i ==> k % d != 0;
  assert i * i > k;

  forall d | i <= d < k
    ensures k % d != 0
  {
    if k % d == 0 {
      var quotient := k / d;
      assert quotient * d == k;
      assert quotient >= 1;

      if quotient == 1 {
        assert d == k;
        assert false;
      } else {
        assert quotient >= 2;
        assert quotient < i;
        assert k % quotient != 0;
        assert false;
      }
    }
  }

  return true;
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
  requires ValidInput(input)
  ensures var n := StringToInt(input);
          n < 2 ==> result == "1"
  ensures var n := StringToInt(input);
          (n >= 2 && isPrimeResult(n)) ==> result == "1"
  ensures var n := StringToInt(input);
          (n >= 2 && !isPrimeResult(n) && n % 2 == 0) ==> result == "2"
  ensures var n := StringToInt(input);
          (n >= 2 && !isPrimeResult(n) && n % 2 == 1 && n - 2 >= 2 && isPrimeResult(n - 2)) ==> result == "2"
  ensures var n := StringToInt(input);
          (n >= 2 && !isPrimeResult(n) && n % 2 == 1 && (n - 2 < 2 || !isPrimeResult(n - 2))) ==> result == "3"
  ensures result in ["1", "2", "3"]
// </vc-spec>
// <vc-code>
{
  var n := StringToInt(input);

  if n >= 2 {
    var isPrimeN := isPrime(n);
    if isPrimeN {
      return "1";
    } else if n % 2 == 0 {
      return "2";
    } else {
      if n - 2 >= 2 {
        var isPrimeNMinus2 := isPrime(n - 2);
        if isPrimeNMinus2 {
          return "2";
        } else {
          return "3";
        }
      } else {
        return "3";
      }
    }
  } else {
    return "1";
  }
}
// </vc-code>
