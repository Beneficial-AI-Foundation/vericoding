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
function CountMedPrefix(p: seq<int>, n: int, i: int): int
    requires ValidInput(n, p)
    requires 0 <= i <= n - 2
{
    |set j | 0 <= j < i && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j|
}

lemma CountMedPrefix_Step(p: seq<int>, n: int, i: int)
    requires ValidInput(n, p)
    requires 0 <= i < n - 2
    ensures CountMedPrefix(p, n, i + 1) ==
            CountMedPrefix(p, n, i) + (if IsMedianOfThree(p[i], p[i + 1], p[i + 2]) then 1 else 0)
{
    var S := set j | 0 <= j < i && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j;
    var T := set j | 0 <= j < i + 1 && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j;

    if IsMedianOfThree(p[i], p[i + 1], p[i + 2]) {
        assert i !in S;
        assert 0 <= i < i + 1;
        assert i in T;
        assert forall x :: x in T <==> x in S || x == i;
        assert T == S + {i};
        assert |S + {i}| == |S| + 1;
        assert CountMedPrefix(p, n, i + 1) == |T|;
        assert CountMedPrefix(p, n, i) == |S|;
    } else {
        assert i !in T;
        assert forall x :: x in T <==> x in S;
        assert T == S;
        assert |T| == |S|;
        assert CountMedPrefix(p, n, i + 1) == |T|;
        assert CountMedPrefix(p, n, i) == |S|;
    }
}

lemma CountMedPrefix_Full(p: seq<int>, n: int)
    requires ValidInput(n, p)
    ensures CountMedPrefix(p, n, n - 2) == CountMedianElements(p, n)
{
    assert CountMedPrefix(p, n, n - 2) ==
        |set j | 0 <= j < n - 2 && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j|;
    assert CountMedianElements(p, n) ==
        |set j | 0 <= j < n - 2 && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j|;
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
  var acc := 0;
  var i := 0;
  while i < n - 2
    invariant 0 <= i <= n - 2
    invariant 0 <= acc <= i
    invariant acc == CountMedPrefix(p, n, i)
    decreases n - 2 - i
  {
    if IsMedianOfThree(p[i], p[i + 1], p[i + 2]) {
      acc := acc + 1;
    }
    CountMedPrefix_Step(p, n, i);
    i := i + 1;
    assert acc == CountMedPrefix(p, n, i);
  }
  result := acc;
  CountMedPrefix_Full(p, n);
}
// </vc-code>

