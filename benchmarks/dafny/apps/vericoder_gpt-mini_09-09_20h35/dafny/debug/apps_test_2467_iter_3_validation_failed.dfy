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
method SortedImpliesRange(s: seq<int>, a: int, b: int)
  requires isSorted(s)
  requires 0 <= a < b < |s|
  ensures s[a] < s[b]
  decreases b - a
{
  if a + 1 == b {
    // direct from isSorted
    assert s[a] < s[a + 1];
    return;
  } else {
    // s[a] < s[a+1] and s[a+1] < s[b] by recursive call -> s[a] < s[b]
    assert s[a] < s[a + 1];
    SortedImpliesRange(s, a + 1, b);
    // transitivity of < yields the result
    return;
  }
}

lemma ExtensionEquiv(temp: seq<int>, combo: seq<int>, k: int, n: int, start: int, i: int)
  requires isValidExtension(temp, combo, k, n, start)
  requires |combo| > |temp|
  requires combo[|temp|] == i
  ensures isValidExtension(temp + [i], combo, k, n, i + 1)
{
  // From isValidExtension(temp, combo, ...):
  // - |combo| == k and sum(combo) == n etc. are already part of the predicate and carry over.
  // Show the prefix equality up to |temp| + 1:
  // For j < |temp|, temp[j] == combo[j] (by isValidExtension)
  // And combo[|temp|] == i equals (temp + [i])[|temp|]
  // Now show for j >= |temp|+1 that combo[j] >= i+1
  var newTemp := temp + [i];
  // prefix property:
  assert forall j :: 0 <= j < |newTemp| ==> newTemp[j] == combo[j]
  {
    var j := j;
    if j < |temp| {
      // inherited from isValidExtension(temp, combo, ...)
      assert temp[j] == combo[j];
    } else {
      // j == |temp|
      assert newTemp[j] == i;
      assert combo[|temp|] == i;
    }
  }

  // Now show for indices >= |newTemp|, combo[j] >= i+1
  assert forall j :: |newTemp| <= j < |combo| ==> combo[j] >= i + 1
  {
    var j := j;
    // Use sortedness of combo to get combo[|temp|] < combo[j]
    SortedImpliesRange(combo, |temp|, j);
    assert combo[|temp|] < combo[j];
    // combo[j] > i implies combo[j] >= i + 1 for integers
    assert combo[j] >= i + 1;
  }
  // Everything required by isValidExtension(newTemp, combo, k, n, i+1) holds:
  // - lengths, sum, bounds 1..9, distinctness, sortedness and prefix are preserved,
  //   and we just established the lower bound for indices >= |newTemp|.
}

method dfs(temp: seq<int>, k: int, n: int, start: int) returns (out: seq<seq<int>>)
  requires k >= |temp|
  requires sum(temp) <= n
  requires forall j :: 0 <= j < |temp| ==> 1 <= temp[j] <= 9
  requires isDistinct(temp)
  requires isSorted(temp)
  // ensures that next chosen element will be strictly larger than the last element of temp (if any)
  requires |temp| == 0 || temp[|temp|-1] < start
  decreases k - |temp|
  ensures forall i :: 0 <= i < |out| ==> isValidExtension(temp, out[i], k, n, start)
  ensures forall combo :: isValidExtension(temp, combo, k, n, start) ==> combo in out
  ensures forall i, j :: 0 <= i <
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
method SortedImpliesRange(s: seq<int>, a: int, b: int)
  requires isSorted(s)
  requires 0 <= a < b < |s|
  ensures s[a] < s[b]
  decreases b - a
{
  if a + 1 == b {
    // direct from isSorted
    assert s[a] < s[a + 1];
    return;
  } else {
    // s[a] < s[a+1] and s[a+1] < s[b] by recursive call -> s[a] < s[b]
    assert s[a] < s[a + 1];
    SortedImpliesRange(s, a + 1, b);
    // transitivity of < yields the result
    return;
  }
}

lemma ExtensionEquiv(temp: seq<int>, combo: seq<int>, k: int, n: int, start: int, i: int)
  requires isValidExtension(temp, combo, k, n, start)
  requires |combo| > |temp|
  requires combo[|temp|] == i
  ensures isValidExtension(temp + [i], combo, k, n, i + 1)
{
  // From isValidExtension(temp, combo, ...):
  // - |combo| == k and sum(combo) == n etc. are already part of the predicate and carry over.
  // Show the prefix equality up to |temp| + 1:
  // For j < |temp|, temp[j] == combo[j] (by isValidExtension)
  // And combo[|temp|] == i equals (temp + [i])[|temp|]
  // Now show for j >= |temp|+1 that combo[j] >= i+1
  var newTemp := temp + [i];
  // prefix property:
  assert forall j :: 0 <= j < |newTemp| ==> newTemp[j] == combo[j]
  {
    var j := j;
    if j < |temp| {
      // inherited from isValidExtension(temp, combo, ...)
      assert temp[j] == combo[j];
    } else {
      // j == |temp|
      assert newTemp[j] == i;
      assert combo[|temp|] == i;
    }
  }

  // Now show for indices >= |newTemp|, combo[j] >= i+1
  assert forall j :: |newTemp| <= j < |combo| ==> combo[j] >= i + 1
  {
    var j := j;
    // Use sortedness of combo to get combo[|temp|] < combo[j]
    SortedImpliesRange(combo, |temp|, j);
    assert combo[|temp|] < combo[j];
    // combo[j] > i implies combo[j] >= i + 1 for integers
    assert combo[j] >= i + 1;
  }
  // Everything required by isValidExtension(newTemp, combo, k, n, i+1) holds:
  // - lengths, sum, bounds 1..9, distinctness, sortedness and prefix are preserved,
  //   and we just established the lower bound for indices >= |newTemp|.
}

method dfs(temp: seq<int>, k: int, n: int, start: int) returns (out: seq<seq<int>>)
  requires k >= |temp|
  requires sum(temp) <= n
  requires forall j :: 0 <= j < |temp| ==> 1 <= temp[j] <= 9
  requires isDistinct(temp)
  requires isSorted(temp)
  // ensures that next chosen element will be strictly larger than the last element of temp (if any)
  requires |temp| == 0 || temp[|temp|-1] < start
  decreases k - |temp|
  ensures forall i :: 0 <= i < |out| ==> isValidExtension(temp, out[i], k, n, start)
  ensures forall combo :: isValidExtension(temp, combo, k, n, start) ==> combo in out
  ensures forall i, j :: 0 <= i <
// </vc-code>

