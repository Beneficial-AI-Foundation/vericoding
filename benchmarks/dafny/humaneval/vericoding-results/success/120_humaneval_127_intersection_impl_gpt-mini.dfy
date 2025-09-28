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
lemma OverlapLengthPositive(start1: int, end1: int, start2: int, end2: int)
  requires start1 <= end1 && start2 <= end2
  requires max(start1, start2) <= min(end1, end2)
  ensures min(end1, end2) - max(start1, start2) + 1 >= 1
{
  assert min(end1, end2) - max(start1, start2) >= 0;
  assert min(end1, end2) - max(start1, start2) + 1 >= 1;
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
  var overlapStart := max(start1, start2);
  var overlapEnd := min(end1, end2);
  if overlapStart <= overlapEnd {
    var length := overlapEnd - overlapStart + 1;
    OverlapLengthPositive(start1, end1, start2, end2);
    if IsPrime(length as nat) {
      result := "YES";
    } else {
      result := "NO";
    }
  } else {
    result := "NO";
  }
}

// </vc-code>
