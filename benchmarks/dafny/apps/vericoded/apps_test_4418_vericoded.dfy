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
function progress(s: seq<int>): int
  requires |s| == 7
{
  s[1] + 2*s[2] + 3*s[3] + 4*s[4] + 5*s[5] + 6*s[6]
}

lemma UpdateState_progress_bound(s: seq<int>, ai: int, k: seq<int>)
  requires |s| == 7 && |k| == 6
  requires ai in {4, 8, 15, 16, 23, 42}
  requires k == [4, 8, 15, 16, 23, 42]
  requires forall i :: 0 <= i < 7 ==> s[i] >= 0
  ensures progress(update_state(s, ai, k)) <= progress(s) + 1
{
  if ai == k[5] && s[5] > 0 {
    assert update_state(s, ai, k) == s[6 := s[6] + 1][5 := s[5] - 1];
    calc {
      progress(update_state(s, ai, k));
      == { }
      s[1] + 2*s[2] + 3*s[3] + 4*s[4] + 5*(s[5] - 1) + 6*(s[6] + 1);
      == { }
      s[1] + 2*s[2] + 3*s[3] + 4*s[4] + 5*s[5] - 5 + 6*s[6] + 6;
      == { }
      progress(s) + 1;
    }
  } else if ai == k[4] && s[4] > 0 {
    assert update_state(s, ai, k) == s[5 := s[5] + 1][4 := s[4] - 1];
    calc {
      progress(update_state(s, ai, k));
      == { }
      s[1] + 2*s[2] + 3*s[3] + 4*(s[4] - 1) + 5*(s[5] + 1) + 6*s[6];
      == { }
      s[1] + 2*s[2] + 3*s[3] + 4*s[4] - 4 + 5*s[5] + 5 + 6*s[6];
      == { }
      progress(s) + 1;
    }
  } else if ai == k[3] && s[3] > 0 {
    assert update_state(s, ai, k) == s[4 := s[4] + 1][3 := s[3] - 1];
    calc {
      progress(update_state(s, ai, k));
      == { }
      s[1] + 2*s[2] + 3*(s[3] - 1) + 4*(s[4] + 1) + 5*s[5] + 6*s[6];
      == { }
      s[1] + 2*s[2] + 3*s[3] - 3 + 4*s[4] + 4 + 5*s[5] + 6*s[6];
      == { }
      progress(s) + 1;
    }
  } else if ai == k[2] && s[2] > 0 {
    assert update_state(s, ai, k) == s[3 := s[3] + 1][2 := s[2] - 1];
    calc {
      progress(update_state(s, ai, k));
      == { }
      s[1] + 2*(s[2] - 1) + 3*(s[3] + 1) + 4*s[4] + 5*s[5] + 6*s[6];
      == { }
      s[1] + 2*s[2] - 2 + 3*s[3] + 3 + 4*s[4] + 5*s[5] + 6*s[6];
      == { }
      progress(s) + 1;
    }
  } else if ai == k[1] && s[1] > 0 {
    assert update_state(s, ai, k) == s[2 := s[2] + 1][1 := s[1] - 1];
    calc {
      progress(update_state(s, ai, k));
      == { }
      (s[1] - 1) + 2*(s[2] + 1) + 3*s[3] + 4*s[4] + 5*s[5] + 6*s[6];
      == { }
      s[1] - 1 + 2*s[2] + 2 + 3*s[3] + 4*s[4] + 5*s[5] + 6*s[6];
      == { }
      progress(s) + 1;
    }
  } else if ai == k[0] && s[0] > 0 {
    assert update_state(s, ai, k) == s[1 := s[1] + 1][0 := s[0] - 1];
    calc {
      progress(update_state(s, ai, k));
      == { }
      (s[1] + 1) + 2*s[2] + 3*s[3] + 4*s[4] + 5*s[5] + 6*s[6];
      == { }
      s[1] + 1 + 2*s[2] + 3*s[3] + 4*s[4] + 5*s[5] + 6*s[6];
      == { }
      progress(s) + 1;
    }
  } else {
    assert update_state(s, ai, k) == s;
    calc {
      progress(update_state(s, ai, k));
      == { }
      progress(s);
    }
  }
}

lemma ProcessArray_progress_bound(s: seq<int>, a: seq<int>, k: seq<int>, index: int)
  requires |s| == 7 && |k| == 6
  requires 0 <= index <= |a|
  requires forall i :: 0 <= i < |a| ==> a[i] in {4, 8, 15, 16, 23, 42}
  requires k == [4, 8, 15, 16, 23, 42]
  requires forall i :: 0 <= i < 7 ==> s[i] >= 0
  decreases |a| - index
  ensures progress(process_array(s, a, k, index)) <= progress(s) + |a| - index
{
  if index == |a| {
    // base case: no steps, progress unchanged
    assert process_array(s, a, k, index) == s;
    calc {
      progress(process_array(s, a, k, index));
      == { }
      progress(s);
      <= { } progress(s) + |a| - index;
    }
  } else {
    var ai := a[index];
    var new_s := update_state(s, ai, k);
    // by definition of process_array when index < |a|
    assert process_array(s, a, k, index) == process_array(new_s, a, k, index + 1);
    UpdateState_progress_bound(s, ai, k);
    assert progress(new_s) <= progress(s) + 1;
    ProcessArray_progress_bound(new_s, a, k, index + 1);
    calc {
      progress(process_array(s, a, k, index));
      == { }
      progress(process_array(new_s, a, k, index + 1));
      <= { } progress(new_s) + |a| - (index + 1);
      <= { } progress(s) + 1 + |a| - (index + 1);
      == { } progress(s) + |a| - index;
    }
  }
}

lemma NumberOfComplete_subsequences_bound(n: int, a: seq<int>)
  requires ValidInput(n, a)
  ensures 6 * number_of_complete_subsequences(n, a) <= n
{
  var s := [n, 0, 0, 0, 0, 0, 0];
  var k := [4, 8, 15, 16, 23, 42];
  var final_s := process_array(s, a, k, 0);
  ProcessArray_progress_bound(s, a, k, 0);
  // progress(final_s) <= progress(s) + |a| - 0 = 0 + n
  assert progress(final_s) <= n;
  // progress(final_s) >= 6 * final_s[6]
  assert progress(final_s) >= 6 * final_s[6];
  assert final_s[6] == number_of_complete_subsequences(n, a);
  calc {
    6 * number_of_complete_subsequences(n, a);
    == { }
    6 * final_s[6];
    <= { } progress(final_s);
    <= { } n;
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
  var count := number_of_complete_subsequences(n, a);
  NumberOfComplete_subsequences_bound(n, a);
  assert 6 * count <= n;
  result := n - 6 * count;
}
// </vc-code>

