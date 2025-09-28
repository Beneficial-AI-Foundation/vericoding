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
  function OverlapLength(a1: int, a2: int, b1: int, b2: int): (len: int)
    requires a1 <= a2 && b1 <= b2
    ensures len == max(0, min(a2, b2) - max(a1, b1) + 1)
    ensures len >= 0
  {
    var overlapStart := max(a1, b1);
    var overlapEnd := min(a2, b2);
    if overlapStart <= overlapEnd then overlapEnd - overlapStart + 1 else 0
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
  /* code modified by LLM (iteration 2): Fixed syntax error in condition */
  var overlapStart := max(start1, start2);
  var overlapEnd := min(end1, end2);
  
  if overlapStart <= overlapEnd {
    var length := overlapEnd - overlapStart + 1;
    result := if IsPrime(length as nat) then "YES" else "NO";
  } else {
    result := "NO";
  }
}
// </vc-code>
