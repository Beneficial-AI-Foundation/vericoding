predicate ValidInput(n: int, a: seq<int>)
{
    n >= 0 && |a| == n && forall i :: 0 <= i < |a| ==> a[i] in {4, 8, 15, 16, 23, 42}
}

function number_of_complete_subsequences(n: int, a: seq<int>): int
  requires ValidInput(n, a)
  ensures 0 <= number_of_complete_subsequences(n, a) <= n
{
    var k := [4, 8, 15, 16, 23, 42];
    var s := [n, 0, 0, 0, 0, 0, 0];
    var final_s := process_array(s, a, k, 0);
    final_s[6]
}

function process_array(s: seq<int>, a: seq<int>, k: seq<int>, index: int): seq<int>
  requires |s| == 7 && |k| == 6
  requires 0 <= index <= |a|
  requires forall i :: 0 <= i < |a| ==> a[i] in {4, 8, 15, 16, 23, 42}
  requires k == [4, 8, 15, 16, 23, 42]
  requires forall i :: 0 <= i < 7 ==> s[i] >= 0
  ensures |process_array(s, a, k, index)| == 7
  ensures forall i :: 0 <= i < 7 ==> process_array(s, a, k, index)[i] >= 0
  ensures s[0] + s[1] + s[2] + s[3] + s[4] + s[5] + s[6] == process_array(s, a, k, index)[0] + process_array(s, a, k, index)[1] + process_array(s, a, k, index)[2] + process_array(s, a, k, index)[3] + process_array(s, a, k, index)[4] + process_array(s, a, k, index)[5] + process_array(s, a, k, index)[6]
  ensures process_array(s, a, k, index)[6] <= s[0] + s[1] + s[2] + s[3] + s[4] + s[5] + s[6]
  ensures index < |a| ==> process_array(s, a, k, index) == process_array(update_state(s, a[index], k), a, k, index + 1)
  decreases |a| - index
{
    if index == |a| then s
    else
        var ai := a[index];
        var new_s := update_state(s, ai, k);
        process_array(new_s, a, k, index + 1)
}

function update_state(s: seq<int>, ai: int, k: seq<int>): seq<int>
  requires |s| == 7 && |k| == 6
  requires ai in {4, 8, 15, 16, 23, 42}
  requires k == [4, 8, 15, 16, 23, 42]
  requires forall i :: 0 <= i < 7 ==> s[i] >= 0
  ensures |update_state(s, ai, k)| == 7
  ensures forall i :: 0 <= i < 7 ==> update_state(s, ai, k)[i] >= 0
  ensures s[0] + s[1] + s[2] + s[3] + s[4] + s[5] + s[6] == update_state(s, ai, k)[0] + update_state(s, ai, k)[1] + update_state(s, ai, k)[2] + update_state(s, ai, k)[3] + update_state(s, ai, k)[4] + update_state(s, ai, k)[5] + update_state(s, ai, k)[6]
{
    if ai == k[5] && s[5] > 0 then s[6 := s[6] + 1][5 := s[5] - 1]
    else if ai == k[4] && s[4] > 0 then s[5 := s[5] + 1][4 := s[4] - 1]
    else if ai == k[3] && s[3] > 0 then s[4 := s[4] + 1][3 := s[3] - 1]
    else if ai == k[2] && s[2] > 0 then s[3 := s[3] + 1][2 := s[2] - 1]
    else if ai == k[1] && s[1] > 0 then s[2 := s[2] + 1][1 := s[1] - 1]
    else if ai == k[0] && s[0] > 0 then s[1 := s[1] + 1][0 := s[0] - 1]
    else s
}

function number_of_complete_subsequences_partial(n: int, a: seq<int>, k: seq<int>, index: int): int
  requires ValidInput(n, a)
  requires |k| == 6
  requires k == [4, 8, 15, 16, 23, 42]
  requires 0 <= index <= |a|
  ensures 0 <= number_of_complete_subsequences_partial(n, a, k, index) <= n
{
    var s := [n, 0, 0, 0, 0, 0, 0];
    var partial_a := if index == 0 then [] else a[0..index];
    var final_s := process_array(s, partial_a, k, 0);
    final_s[6]
}

// <vc-helpers>
lemma LemmaSumPreserved(s: seq<int>, a: seq<int>, k: seq<int>, index: int)
  requires |s| == 7 && |k| == 6
  requires 0 <= index <= |a|
  requires forall i :: 0 <= i < |a| ==> a[i] in {4, 8, 15, 16, 23, 42}
  requires k == [4, 8, 15, 16, 23, 42]
  requires forall i :: 0 <= i < 7 ==> s[i] >= 0
  ensures s[0] + s[1] + s[2] + s[3] + s[4] + s[5] + s[6] == 
          process_array(s, a, k, index)[0] + process_array(s, a, k, index)[1] + 
          process_array(s, a, k, index)[2] + process_array(s, a, k, index)[3] + 
          process_array(s, a, k, index)[4] + process_array(s, a, k, index)[5] + 
          process_array(s, a, k, index)[6]
  decreases |a| - index
{
  if index < |a| {
    var ai := a[index];
    var new_s := update_state(s, ai, k);
    LemmaSumPreservedUpdate(s, ai, k);
    LemmaSumPreserved(new_s, a, k, index + 1);
  }
}

lemma LemmaSumPreservedUpdate(s: seq<int>, ai: int, k: seq<int>)
  requires |s| == 7 && |k| == 6
  requires ai in {4, 8, 15, 16, 23, 42}
  requires k == [4, 8, 15, 16, 23, 42]
  requires forall i :: 0 <= i < 7 ==> s[i] >= 0
  ensures s[0] + s[1] + s[2] + s[3] + s[4] + s[5] + s[6] == 
          update_state(s, ai, k)[0] + update_state(s, ai, k)[1] + 
          update_state(s, ai, k)[2] + update_state(s, ai, k)[3] + 
          update_state(s, ai, k)[4] + update_state(s, ai, k)[5] + 
          update_state(s, ai, k)[6]
{
  if ai == k[5] && s[5] > 0 {
  } else if ai == k[4] && s[4] > 0 {
  } else if ai == k[3] && s[3] > 0 {
  } else if ai == k[2] && s[2] > 0 {
  } else if ai == k[1] && s[1] > 0 {
  } else if ai == k[0] && s[0] > 0 {
  } else {
  }
}

lemma LemmaTotalMinusComplete(n: int, a: seq<int>)
  requires ValidInput(n, a)
  ensures n - 6 * number_of_complete_subsequences(n, a) >= 0
{
  var final_s := process_array([n, 0, 0, 0, 0, 0, 0], a, [4, 8, 15, 16, 23, 42], 0);
  assert final_s[6] == number_of_complete_subsequences(n, a);
  assert final_s[0] + final_s[1] + final_s[2] + final_s[3] + final_s[4] + final_s[5] + final_s[6] == n;
  assert n - 6 * final_s[6] >= 0 by {
    assert final_s[0] >= 0;
    assert final_s[1] >= 0;
    assert final_s[2] >= 0;
    assert final_s[3] >= 0;
    assert final_s[4] >= 0;
    assert final_s[5] >= 0;
    assert final_s[6] >= 0;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
  requires ValidInput(n, a)
  ensures 0 <= result <= n
  ensures result == n - 6 * (number_of_complete_subsequences(n, a))
// </vc-spec>
// <vc-code>
{
  var k := [4, 8, 15, 16, 23, 42];
  var s : seq<int> := [n, 0, 0, 0, 0, 0, 0];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |s| == 7
    invariant forall j :: 0 <= j < 7 ==> s[j] >= 0
    invariant s[0] + s[1] + s[2] + s[3] + s[4] + s[5] + s[6] == n
    invariant s == process_array([n, 0, 0, 0, 0, 0, 0], a[0..i], k, 0)
  {
    var ai := a[i];
    s := update_state(s, ai, k);
    i := i + 1;
    LemmaSumPreservedUpdate(s, ai, k);
  }
  result := n - 6 * s[6];
  LemmaTotalMinusComplete(n, a);
}
// </vc-code>

