// <vc-preamble>

datatype Option<T> = None | Some(value: T)

function abs(x: int): int
{
    if x >= 0 then x else -x
}

function sign(x: int): int
{
    if x > 0 then 1 else if x < 0 then -1 else 0
}

function sum_of_magnitudes(arr: seq<int>): int
{
    if |arr| == 0 then 0 else abs(arr[0]) + sum_of_magnitudes(arr[1..])
}

function product_of_signs(arr: seq<int>): int
{
    if |arr| == 0 then 1 else sign(arr[0]) * product_of_signs(arr[1..])
}
lemma sum_of_magnitudes_append(arr: seq<int>, i: int)
    requires 0 <= i < |arr|
    ensures sum_of_magnitudes(arr[0..i+1]) == sum_of_magnitudes(arr[0..i]) + abs(arr[i])
{
    if i == 0 {
        assert arr[0..1] == [arr[0]];
        assert arr[0..0] == [];
    } else {
        sum_of_magnitudes_append(arr[1..], i-1);
        assert arr[1..][0..i-1] == arr[1..i];
        assert arr[1..][0..i] == arr[1..i+1];
        assert sum_of_magnitudes(arr[1..i+1]) == sum_of_magnitudes(arr[1..i]) + abs(arr[i]);
        assert sum_of_magnitudes(arr[0..i+1]) == abs(arr[0]) + sum_of_magnitudes(arr[1..i+1]);
        assert sum_of_magnitudes(arr[0..i]) == abs(arr[0]) + sum_of_magnitudes(arr[1..i]);
    }
}

lemma product_of_signs_append(arr: seq<int>, i: int)
    requires 0 <= i < |arr|
    ensures product_of_signs(arr[0..i+1]) == product_of_signs(arr[0..i]) * sign(arr[i])
{
    if i == 0 {
        assert arr[0..1] == [arr[0]];
        assert arr[0..0] == [];
    } else {
        product_of_signs_append(arr[1..], i-1);
        assert arr[1..][0..i-1] == arr[1..i];
        assert arr[1..][0..i] == arr[1..i+1];
        assert product_of_signs(arr[1..i+1]) == product_of_signs(arr[1..i]) * sign(arr[i]);
        assert product_of_signs(arr[0..i+1]) == sign(arr[0]) * product_of_signs(arr[1..i+1]);
        assert product_of_signs(arr[0..i]) == sign(arr[0]) * product_of_signs(arr[1..i]);
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method prod_signs(arr: seq<int>) returns (result: Option<int>)
    ensures |arr| == 0 ==> result == None
    ensures |arr| > 0 ==> result == Some(sum_of_magnitudes(arr) * product_of_signs(arr))
// </vc-spec>
// <vc-code>
{
  if |arr| == 0 {
    result := None;
  } else {
    var sum := 0;
    var prod := 1;
    var i := 0;
    
    while i < |arr|
      invariant 0 <= i <= |arr|
      invariant sum == sum_of_magnitudes(arr[0..i])
      invariant prod == product_of_signs(arr[0..i])
    {
      sum := sum + abs(arr[i]);
      prod := prod * sign(arr[i]);
      sum_of_magnitudes_append(arr, i);
      product_of_signs_append(arr, i);
      i := i + 1;
    }
    
    assert arr[0..|arr|] == arr;
    result := Some(sum * prod);
  }
}
// </vc-code>
