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
predicate NonEmptyIntersection(start1: int, end1: int, start2: int, end2: int)
{
  max(start1, start2) <= min(end1, end2)
}

function IntersectionLength(start1: int, end1: int, start2: int, end2: int): nat
  requires start1 <= end1 && start2 <= end2
  requires NonEmptyIntersection(start1, end1, start2, end2)
{
  (min(end1, end2) - max(start1, start2) + 1) as nat
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
  var s := max(start1, start2);
  var e := min(end1, end2);
  if s <= e {
    var len: nat := (e - s + 1) as nat;
    if IsPrime(len) {
      result := "YES";
    } else {
      result := "NO";
    }
  } else {
    result := "NO";
  }
}
// </vc-code>
