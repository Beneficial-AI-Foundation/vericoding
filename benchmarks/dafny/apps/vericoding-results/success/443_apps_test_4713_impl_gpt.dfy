function MaxValue(S: string): int
{
    MaxValueUpToIndex(S, |S|)
}

function MaxValueUpToIndex(S: string, upTo: int): int
    requires 0 <= upTo <= |S|
{
    if upTo == 0 then 0
    else 
        var currentValue := CurrentValueAtIndex(S, upTo);
        var maxBefore := MaxValueUpToIndex(S, upTo - 1);
        if currentValue > maxBefore then currentValue else maxBefore
}

function CurrentValueAtIndex(S: string, index: int): int
    requires 0 <= index <= |S|
{
    if index == 0 then 0
    else CurrentValueAtIndex(S, index - 1) + (if S[index - 1] == 'I' then 1 else -1)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(N: int, S: string) returns (result: int)
    requires 1 <= N <= 100
    requires N == |S|
    requires forall i :: 0 <= i < |S| ==> S[i] == 'I' || S[i] == 'D'
    ensures result >= 0
    ensures result == MaxValue(S)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var cur := 0;
  var mx := 0;

  while i < N
    invariant 0 <= i <= N
    invariant cur == CurrentValueAtIndex(S, i)
    invariant mx == MaxValueUpToIndex(S, i)
    invariant mx >= 0
    decreases N - i
  {
    assert N == |S|;
    assert 0 <= i < |S|;

    var delta := if S[i] == 'I' then 1 else -1;

    assert 0 <= i + 1 <= |S|;
    assert CurrentValueAtIndex(S, i + 1) ==
      CurrentValueAtIndex(S, (i + 1) - 1) + (if S[(i + 1) - 1] == 'I' then 1 else -1);

    var newCur := cur + delta;
    assert newCur == CurrentValueAtIndex(S, i) + (if S[i] == 'I' then 1 else -1);
    assert newCur == CurrentValueAtIndex(S, i + 1);
    cur := newCur;

    assert MaxValueUpToIndex(S, i + 1) ==
      (if CurrentValueAtIndex(S, i + 1) > MaxValueUpToIndex(S, i)
       then CurrentValueAtIndex(S, i + 1) else MaxValueUpToIndex(S, i));

    var newMx := if cur > mx then cur else mx;
    assert newMx == (if CurrentValueAtIndex(S, i + 1) > MaxValueUpToIndex(S, i)
                     then CurrentValueAtIndex(S, i + 1) else MaxValueUpToIndex(S, i));
    mx := newMx;

    i := i + 1;
  }

  result := mx;
}
// </vc-code>

