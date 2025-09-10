predicate is_valid_beautiful_arrangement(arrangement: seq<int>, sizes: seq<int>)
    requires forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= |sizes|
{
    |arrangement| >= 1 &&
    // All indices are distinct
    (forall i, j :: 0 <= i < j < |arrangement| ==> arrangement[i] != arrangement[j]) &&
    // Indices are in increasing order
    (forall i :: 0 <= i < |arrangement| - 1 ==> arrangement[i] < arrangement[i + 1]) &&
    // Adjacent elements satisfy divisibility constraint
    (forall i :: 0 <= i < |arrangement| - 1 ==> arrangement[i + 1] % arrangement[i] == 0) &&
    // Adjacent elements satisfy size constraint
    (forall i :: 0 <= i < |arrangement| - 1 ==> sizes[arrangement[i] - 1] < sizes[arrangement[i + 1] - 1])
}

predicate ValidInput(n: int, sizes: seq<int>)
{
    n >= 1 && |sizes| == n && forall i :: 0 <= i < n ==> sizes[i] >= 1
}

// <vc-helpers>
method find_max_arrangement(position: int, used: set<int>, sizes: seq<int>) returns (len: int, arr: seq<int>)
  requires 1 <= position <= |sizes| + 1
  requires forall x :: x in used ==> 1 <= x <= |sizes|
  requires forall x, y :: x in used && y in used && x != y ==> x != y
  decreases |sizes| - position + 1
  ensures |arr| == len
  ensures |arr| == 0 || is_valid_beautiful_arrangement(arr, sizes)
  ensures forall extension_arr :: |extension_arr| >= 1 && is_valid_beautiful_arrangement(extension_arr, sizes) ==> |extension_arr| <= len
{
  if position == |sizes| + 1 {
    len := 0;
    arr := [];
  } else {
    // Consider not taking the current position
    var len_not_take, arr_not_take := find_max_arrangement(position + 1, used, sizes);
    len := len_not_take;
    arr := arr_not_take;

    // Consider taking the current position if possible
    if position !in used {
      var len_take, arr_take := find_max_arrangement(position + 1, used + {position}, sizes);
      var candidate_len := len_take + 1;
      var candidate_arr := [position] + arr_take;
      if candidate_len == 1 || (candidate_arr[1] % candidate_arr[0] == 0 && sizes[candidate_arr[0] - 1] < sizes[candidate_arr[1] - 1]) {
        if candidate_len > len {
          len := candidate_len;
          arr := candidate_arr;
        }
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, sizes: seq<int>) returns (result: int)
    requires ValidInput(n, sizes)
    ensures 1 <= result <= n
    ensures forall arrangement :: (forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= |sizes|) && is_valid_beautiful_arrangement(arrangement, sizes) ==> |arrangement| <= result
    ensures exists arrangement :: (forall i :: 0 <= i < |arrangement| ==> 1 <= arrangement[i] <= |sizes|) && is_valid_beautiful_arrangement(arrangement, sizes) && |arrangement| == result
// </vc-spec>
// <vc-code>
{
  var l, a := find_max_arrangement(1, {}, sizes);
  result := l;
}
// </vc-code>

