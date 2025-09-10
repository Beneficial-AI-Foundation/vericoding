predicate ValidInput(n: int, p: seq<int>)
{
    |p| == n && n >= 3
}

function CountMedianElements(p: seq<int>, n: int): int
    requires ValidInput(n, p)
{
    |set i | 0 <= i < n - 2 && IsMedianOfThree(p[i], p[i + 1], p[i + 2]) :: i|
}

predicate IsMedianOfThree(a: int, b: int, c: int)
{
    (a < b < c) || (a > b > c)
}

// <vc-helpers>
function {:inline} CountUpTo(p: seq<int>, i: int): int
  requires 0 <= i <= |p| - 2
{
  |set j | {:trigger IsMedianOfThree(p[j], p[j+1], p[j+2])} 0 <= j < i && IsMedianOfThree(p[j], p[j+1], p[j+2]) :: j|
}

lemma CountUpTo_at_nminus2(n: int, p: seq<int>)
  requires ValidInput(n, p)
  ensures CountUpTo(p, n - 2) == CountMedianElements(p, n)
{
  // Unfold both definitions: they are the same set comprehension
  assert CountUpTo(p, n - 2) == |set j | 0 <= j < n - 2 && IsMedianOfThree(p[j], p[j+1], p[j+2]) :: j|;
  assert CountMedianElements(p, n) == |set j | 0 <= j < n - 2 && IsMedianOfThree(p[j], p[j+1], p[j+2]) :: j|;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: seq<int>) returns (result: int)
    requires ValidInput(n, p)
    ensures result >= 0
    ensures result <= n - 2
    ensures result == CountMedianElements(p, n)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := 0;
  while i < n - 2
    decreases n - 2 - i
    invariant 0 <= i <= n - 2
    invariant result == CountUpTo(p, i)
    invariant 0 <= result <= n - 2
  {
    if IsMedianOfThree(p[i], p[i+1], p[i+2]) {
      result := result + 1;
    }
    i := i + 1;
  }
  ghost CountUpTo_at_nminus2(n, p);
  assert result == CountMedianElements(p, n);
}
// </vc-code>

