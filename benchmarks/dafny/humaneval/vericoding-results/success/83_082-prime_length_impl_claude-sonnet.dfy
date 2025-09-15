// <vc-preamble>
function IsPrime(n: int) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>
function IsStringLengthPrime(s: string): bool
{
  IsPrime(|s|)
}

lemma StringLengthNonNegative(s: string)
  ensures |s| >= 0
{
}

function ModuloHelper(a: int, b: int): int
  requires b > 0
{
  a % b
}
// </vc-helpers>

// <vc-spec>
method PrimeLength(s: string) returns (p : bool)

  ensures p <==> IsPrime(|s|)
// </vc-spec>
// <vc-code>
{
  var len := |s|;
  
  if len <= 1 {
    p := false;
  } else {
    p := true;
    var k := 2;
    while k < len
      invariant 2 <= k <= len
      invariant p <==> (forall j :: 2 <= j < k ==> len % j != 0)
    {
      if len % k == 0 {
        p := false;
        break;
      }
      k := k + 1;
    }
  }
}
// </vc-code>
