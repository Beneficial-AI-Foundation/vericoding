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
  ensures (arr == [] && len == 0) || (is_valid_beautiful_arrangement(arr, sizes) && len >= 1 && arr[0] == position)
  ensures forall extension_arr :: is_valid_beautiful_arrangement(extension_arr, sizes) && |extension_arr| >= 0 ==> |extension_arr| <= len
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
    if position notin used {
      var len_take, arr_take := find_max_arrangement(position + 1, used + {position}, sizes);
      len_take := len_take + 1;
      arr_take := [position] + arr_take;

      if (|arr_take| > 1) {
        assert arr_take[1] % arr_take[0] == 0 && sizes[arr_take[0] - 1] < sizes[arr_take[1] - 1];
      }
      if (len_take > len) {
        len := len_take;
        arr := arr_take;
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
  assert a == [] || is_valid_beautiful_arrangement(a, sizes);
  assert a == [] || |a| == l;
  result := l;
}
// </vc-code>

