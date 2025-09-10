predicate ValidInput(n: int, aa: seq<int>)
{
    n >= 2 &&
    |aa| == n - 1 &&
    forall i :: 0 <= i < |aa| ==> 1 <= aa[i] < i + 2
}

function SubordinateCount(aa: seq<int>, boss_id: int): int
{
    |set j | 0 <= j < |aa| && aa[j] == boss_id|
}

predicate ValidOutput(n: int, aa: seq<int>, result: seq<int>)
{
    |result| == n &&
    forall i :: 0 <= i < n ==> result[i] >= 0 &&
    forall i :: 0 <= i < n ==> result[i] == SubordinateCount(aa, i + 1)
}

// <vc-helpers>
function CountOccurrences(s: seq<int>, value: int): int
  decreases |s|
{
  if |s| == 0 then
    0
  else
    (if s[0] == value then 1 else 0) + CountOccurrences(s[1..], value)
}
lemma CountOccurrencesLemma(s: seq<int>, value: int)
  ensures CountOccurrences(s, value) == |set j | 0 <= j < |s| && s[j] == value|
{
  if |s| == 0 {
    // Base case: trivially true
  } else {
    CountOccurrencesLemma(s[1..], value);
    if s[0] == value {
      calc {
        CountOccurrences(s, value);
        { assert s[0] == value; }
        1 + CountOccurrences(s[1..], value);
        { reveal CountOccurrencesLemma(); }
        1 + |set j | 0 <= j < |s[1..]| && s[1..][j] == value|;
        {
          assert forall k :: 0 <= k < |s[1..]| ==> (s[1..][k] == value) == (s[k+1] == value);
          assert |set j | 0 <= j < |s| && s[j] == value| == 1 + |set j | 1 <= j < |s| && s[j] == value|;
          assert |set j | 0 <= j < |s[1..]| && s[1..][j] == value| == |set j | 1 <= j < |s| && s[j] == value|;
        }
        |set j | 0 <= j < |s| && s[j] == value|;
      }
    } else {
      calc {
        CountOccurrences(s, value);
        { assert s[0] != value; }
        0 + CountOccurrences(s[1..], value);
        { reveal CountOccurrencesLemma(); }
        |set j | 0 <= j < |s[1..]| && s[1..][j] == value|;
        {
          assert forall k :: 0 <= k < |s[1..]| ==> (s[1..][k] == value) == (s[k+1] == value);
          assert |set j | 0 <= j < |s| && s[j] == value| == |set j | 1 <= j < |s| && s[j] == value|;
          assert |set j | 0 <= j < |s[1..]| && s[1..][j] == value| == |set j | 1 <= j < |s| && s[j] == value|;
        }
        |set j | 0 <= j < |s| && s[j] == value|;
      }
    }
  }
}

lemma SubordinateCountMatch(aa: seq<int>, boss_id: int)
    ensures SubordinateCount(aa, boss_id) == CountOccurrences(aa, boss_id)
{
    CountOccurrencesLemma(aa, boss_id);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, aa: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, aa)
    ensures ValidOutput(n, aa, result)
// </vc-spec>
// <vc-code>
{
  var result_arr: array<int> := new int[n];

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> result_arr[k] == SubordinateCount(aa, k + 1)
  {
    var current_boss_id := i + 1;
    SubordinateCountMatch(aa, current_boss_id);
    result_arr[i] := CountOccurrences(aa, current_boss_id);
    i := i + 1;
  }

  result := result_arr[..];
}
// </vc-code>

