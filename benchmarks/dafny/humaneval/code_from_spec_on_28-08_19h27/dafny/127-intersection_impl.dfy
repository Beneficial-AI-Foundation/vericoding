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

// <vc-helpers>
lemma IntersectionLength(start1: int, end1: int, start2: int, end2: int)
  requires start1 <= end1 && start2 <= end2
  ensures var intersectionStart := max(start1, start2);
          var intersectionEnd := min(end1, end2);
          intersectionStart <= intersectionEnd ==> intersectionEnd - intersectionStart + 1 >= 1
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def intersection(interval1: Tuple[Int, Int], interval2: Tuple[Int, Int]) -> str
You are given two intervals, where each interval is a pair of integers. For example, interval = (start, end) = (1, 2). The given intervals are closed which means that the interval (start, end) includes both start and end. For each given interval, it is assumed that its start is less or equal its end. Your task is to determine whether the length of intersection of these two intervals is a prime number. Example, the intersection of the intervals (1, 3), (2, 4) is (2, 3) which its length is 1, which not a prime number. If the length of the intersection is a prime number, return "YES", otherwise, return "NO". If the two intervals don't intersect, return "NO".
*/
// </vc-description>

// <vc-spec>
method Intersection(start1: int, end1: int, start2: int, end2: int) returns (result: string)
  requires start1 <= end1 && start2 <= end2
  ensures result == "YES" || result == "NO"
  ensures var intersectionStart := max(start1, start2);
          var intersectionEnd := min(end1, end2);
          intersectionStart <= intersectionEnd ==>
            (result == "YES" <==> IsPrime(intersectionEnd - intersectionStart + 1))
  ensures var intersectionStart := max(start1, start2);
          var intersectionEnd := min(end1, end2);
          intersectionStart > intersectionEnd ==> result == "NO"
// </vc-spec>
// <vc-code>
{
  var intersectionStart := max(start1, start2);
  var intersectionEnd := min(end1, end2);
  
  if intersectionStart > intersectionEnd {
    result := "NO";
  } else {
    var length := intersectionEnd - intersectionStart + 1;
    if IsPrime(length) {
      result := "YES";
    } else {
      result := "NO";
    }
  }
}
// </vc-code>

method {:test} Main()
{
  var result1 := Intersection(1, 2, 2, 3);
  assert result1 == "NO";
  var result2 := Intersection(-1, 1, 0, 4);
  // The intersection is [0, 1], which has length 2, a prime number
  assert result2 == "YES";
  var result3 := Intersection(-3, -1, -5, 5);
  assert result3 == "YES";
  print "All tests passed!\n";
}