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
  var intersect_start := max(start1, start2);
  var intersect_end := min(end1, end2);

  if intersect_start <= intersect_end {
    var length := (intersect_end - intersect_start + 1) as nat;
    if IsPrime(length) {
      result := "YES";
    } else {
      result := "NO";
    }
  } else {
    result := "NO";
  }
}
// </vc-code>
