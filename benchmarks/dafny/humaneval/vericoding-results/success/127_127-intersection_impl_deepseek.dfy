// <vc-preamble>
function IsPrime(n: nat) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}
function min(a: int, b: int): int
{
  if a <= b then a else b
}
function max(a: int, b: int): int
{
  if a >= b then a else b
}
// </vc-preamble>

// <vc-helpers>
lemma HelperLemma(commonStart: int, commonEnd: int, start1: int, start2: int, end1: int, end2: int)
  requires start1 <= end1 && start2 <= end2
  ensures commonStart == max(start1, start2) && commonEnd == min(end1, end2) ==> (commonStart <= commonEnd <==> max(start1, start2) <= min(end1, end2))
{
}

predicate HasPrimeLength(commonStart: int, commonEnd: int)
  requires commonStart <= commonEnd
{
  IsPrime((commonEnd - commonStart + 1) as nat)
}
// </vc-helpers>

// <vc-spec>
method Intersection(start1: int, end1: int, start2: int, end2: int) returns (result: string)

  requires start1 <= end1 && start2 <= end2

  ensures result == "YES" || result == "NO"
  ensures result == "YES" <==>
    (max(start1, start2) <= min(end1, end2) &&
     IsPrime((min(end1, end2) - max(start1, start2) + 1) as nat))
// </vc-spec>
// <vc-code>
{
  var commonStart := max(start1, start2);
  var commonEnd := min(end1, end2);
  
  if commonStart <= commonEnd && HasPrimeLength(commonStart, commonEnd) {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>
