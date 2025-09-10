function sum(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + sum(s[1..])
}

predicate isDistinct(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

predicate isSorted(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i + 1]
}

predicate isValidCombination(combo: seq<int>, k: int, n: int)
{
    |combo| == k &&
    sum(combo) == n &&
    (forall j :: 0 <= j < |combo| ==> 1 <= combo[j] <= 9) &&
    isDistinct(combo) &&
    isSorted(combo)
}

predicate isValidExtension(temp: seq<int>, combo: seq<int>, k: int, n: int, start: int)
{
    |combo| == k &&
    sum(combo) == n &&
    (forall j :: 0 <= j < |combo| ==> 1 <= combo[j] <= 9) &&
    isDistinct(combo) &&
    isSorted(combo) &&
    |combo| >= |temp| &&
    (forall i :: 0 <= i < |temp| ==> temp[i] == combo[i]) &&
    (forall i :: |temp| <= i < |combo| ==> combo[i] >= start)
}

// <vc-helpers>
method dfs(temp: seq<int>, k: int, n: int, start: int) returns (out: seq<seq<int>>)
  requires k >= |temp|
  requires sum(temp) <= n
  requires forall j :: 0 <= j < |temp| ==> 1 <= temp[j] <= 9
  requires isDistinct(temp)
  requires isSorted(temp)
  // ensures that next chosen element will be strictly larger than the last element of temp (if any)
  requires |temp| == 0 || temp[|temp|-1] < start
  requires 1 <= start <= 10
  decreases k - |temp|
  ensures forall i :: 0 <= i < |out| ==> isValidExtension(temp, out[i], k, n, start)
  ensures forall combo :: isValidExtension(temp, combo, k, n, start) ==> combo in out
{
  if |temp| == k {
    if sum(temp) == n {
      out := [temp];
    } else {
      out := [];
    }
    return;
  }

  var remK := k - |temp|;
  var remSum := n - sum(temp);
  out := [];
  var i := start;
  // iterate candidates for the next element
  while i <= 9
    invariant start <= i <= 10
    invariant forall s :: s in out ==> isValidExtension(temp, s, k, n, start)
    invariant forall combo :: isValidExtension(temp, combo, k, n, start) && |combo| > |temp| && combo[|temp|] < i ==> combo in out
  {
    if i > remSum {
      break;
    }
    var newTemp := temp + [i];
    var tails := dfs(newTemp, k, n, i + 1);

    // append tails one by one, converting their guarantee from newTemp to temp via lemma_extend
    var j := 0;
    while j < |tails|
      invariant 0 <= j <= |tails|
      invariant forall s :: s in out ==> isValidExtension(temp, s, k, n, start)
      invariant forall combo :: isValidExtension(temp, combo, k, n, start) && |combo| > |temp| && combo[|temp|] < i ==> combo in out
    {
      var s := tails[j];
      // from the postcondition of dfs(newTemp,...) we have isValidExtension(newTemp, s, k, n, i+1)
      assert 0 <= j < |tails|;
      assert forall idx :: 0 <= idx < |tails| ==> isValidExtension(newTemp, tails[idx], k, n, i + 1);
      assert isValidExtension(newTemp, s, k, n, i + 1);
      lemma_extend(temp, i, s, k, n, start);
      // now s satisfies isValidExtension(temp, s, k, n, start)
      out := out + [s];
      j := j + 1;
    }

    i := i + 1;
  }
  return;
}

lemma lemma_extend(temp: seq<int>, next: int, combo: seq<int>, k: int, n: int, start: int)
  requires 1 <= start <= 10
  requires 0 <= |temp|
  requires isValidExtension(temp + [next], combo, k, n, next + 1)
  requires next >= start
  ensures isValidExtension(temp, combo, k, n, start)
{
  // unpack facts from isValidExtension(temp + [next], combo, k, n, next + 1)
  assert |combo| == k;
  assert sum(combo) == n;
  assert forall j :: 0 <= j < |combo| ==> 1 <= combo[j] <= 9;
  assert isDistinct(combo);
  assert isSorted(combo);
  assert |combo| >= |temp + [next]|;
  assert forall i :: 0 <= i < |temp + [next]| ==> (temp + [next])[i] == combo[i];
  assert forall i :: |temp + [next]| <= i < |combo| ==> combo[i] >= next + 1;

  // show prefix equality for temp
  assert |temp + [next]| == |temp| + 1;
  // For indices 0 <= i < |temp|, (temp + [next])[i] == temp[i], so combo[i] == temp[i]
  assert forall i :: 0 <= i < |temp| ==> temp[i] == combo[i];
  // For indices i with |temp| <= i < |combo|, need combo[i] >= start:
  // - if i == |temp| then combo[|temp|] == (temp + [next])[|temp|] == next >= start
  // - if i > |temp| then i >= |temp| + 1 = |temp + [next]| so combo[i] >= next + 1 >= start + 1 > start
  assert forall i :: |temp| <= i < |combo| ==>
    if i == |temp| then combo[i] >= start else combo[i] >= start;
  // now reconstruct isValidExtension(temp, combo, k, n, start)
  assert |combo| == k;
  assert sum(combo) == n;
  assert forall j :: 0 <= j < |combo| ==> 1 <= combo[j] <= 9;
  assert isDistinct(combo);
  assert isSorted(combo);
  assert |combo| >= |temp|;
  assert forall i :: 0 <= i < |temp| ==> temp[i] == combo[i];
  assert forall i :: |temp| <= i < |combo| ==> combo[i] >= start;
}
// </vc-helpers>

// <vc-spec>
method combinationSum3(k: int, n: int) returns (result: seq<seq<int>>)
    requires k > 0 && n > 0 && k <= 9
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == k
    ensures forall i :: 0 <= i < |result| ==> sum(result[i]) == n
    ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> 1 <= result[i][j] <= 9
    ensures forall i :: 0 <= i < |result| ==> isDistinct(result[i])
    ensures forall i :: 0 <= i < |result| ==> isSorted(result[i])
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
    ensures forall combo :: isValidCombination(combo, k, n) ==> combo in result
    ensures forall combo :: combo in result ==> isValidCombination(combo, k, n)
// </vc-spec>
// <vc-code>
{
  result := dfs([], k, n, 1);
}
// </vc-code>

