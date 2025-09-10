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
lemma MedianProperty(a: int, b: int, c: int)
    ensures IsMedianOfThree(a, b, c) <==> ((a < b < c) || (a > b > c))
{
}

lemma CountProperty(p: seq<int>, n: int)
    requires ValidInput(n, p)
    ensures CountMedianElements(p, n) == |set i | 0 <= i < n - 2 && ((p[i] < p[i+1] < p[i+2]) || (p[i] > p[i+1] > p[i+2])) :: i|
{
    forall i | 0 <= i < n - 2
        ensures IsMedianOfThree(p[i], p[i+1], p[i+2]) <==> ((p[i] < p[i+1] < p[i+2]) || (p[i] > p[i+1] > p[i+2]))
    {
        MedianProperty(p[i], p[i+1], p[i+2]);
    }
}

ghost method MaintainSetEquivalence(p: seq<int>, n: int, i: int, result: int)
  requires ValidInput(n, p)
  requires 0 <= i <= n - 2
  requires result == |set j | 0 <= j < i && IsMedianOfThree(p[j], p[j+1], p[j+2]) :: j|
  ensures result == |set j | 0 <= j < i && ((p[j] < p[j+1] < p[j+2]) || (p[j] > p[j+1] > p[j+2])) :: j|
{
  forall j | 0 <= j < i
    ensures IsMedianOfThree(p[j], p[j+1], p[j+2]) <==> ((p[j] < p[j+1] < p[j+2]) || (p[j] > p[j+1] > p[j+2]))
  {
    MedianProperty(p[j], p[j+1], p[j+2]);
  }
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
    result := 0;
    var i: int := 0;
    while i < n - 2
        invariant 0 <= i <= n - 2
        invariant result == |set j | 0 <= j < i && IsMedianOfThree(p[j], p[j+1], p[j+2]) :: j|
        invariant result <= i
    {
        if IsMedianOfThree(p[i], p[i+1], p[i+2]) {
            result := result + 1;
        }
        i := i + 1;
    }
    CountProperty(p, n);
    MaintainSetEquivalence(p, n, n - 2, result);
}
// </vc-code>

