

// <vc-helpers>
function sum_filtered(numbers: seq<int>, p_indices: seq<int>): int
  reads numbers
  requires forall i :: 0 <= i < |p_indices| ==> 0 <= p_indices[i] < |numbers|
  requires forall i, j :: 0 <= i < j < |p_indices| ==> p_indices[i] < p_indices[j]
{
  if |p_indices| == 0 then 0
  else numbers[p_indices[0]] + sum_filtered(numbers, p_indices[1..])
}

lemma sum_property(numbers: seq<int>, indices_to_sum: seq<bool>)
  requires |numbers| == |indices_to_sum|
  ensures sum(numbers, indices_to_sum) == sum_filtered(numbers, filter_indices(indices_to_sum))
{
  if |numbers| == 0 {
    // Base case: empty sequence
    assert sum(numbers, indices_to_sum) == 0;
    assert filter_indices(indices_to_sum) == [];
    assert sum_filtered(numbers, filter_indices(indices_to_sum)) == 0;
  } else {
    // Inductive step
    var rest_numbers := numbers[1..];
    var rest_indices_to_sum := indices_to_sum[1..];

    // Recursive call for the rest of the sequence
    sum_property(rest_numbers, rest_indices_to_sum);

    // Relate sum and sum_filtered for the current step
    if indices_to_sum[0] {
      calc {
        sum(numbers, indices_to_sum);
        numbers[0] + sum(rest_numbers, rest_indices_to_sum);
        numbers[0] + sum_filtered(rest_numbers, filter_indices(rest_indices_to_sum));
        {
          lemma_sum_filtered_map_plus_one(numbers, filter_indices(rest_indices_to_sum));
        }
        numbers[0] + sum_filtered(numbers, map_plus_one(filter_indices(rest_indices_to_sum)));
        sum_filtered(numbers, [0] + map_plus_one(filter_indices(rest_indices_to_sum)));
        sum_filtered(numbers, filter_indices(indices_to_sum));
      }
    } else {
      calc {
        sum(numbers, indices_to_sum);
        sum(rest_numbers, rest_indices_to_sum);
        sum_filtered(rest_numbers, filter_indices(rest_indices_to_sum));
        {
          lemma_sum_filtered_map_plus_one(numbers, filter_indices(rest_indices_to_sum));
        }
        sum_filtered(numbers, map_plus_one(filter_indices(rest_indices_to_sum)));
        sum_filtered(numbers, filter_indices(indices_to_sum));
      }
    }
  }
}

lemma lemma_sum_filtered_map_plus_one(numbers: seq<int>, indices: seq<int>)
  requires |numbers| > 0
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |numbers[1..]|
  requires forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j]
  ensures sum_filtered(numbers, map_plus_one(indices)) == sum_filtered(numbers[1..], indices)
{
  if |indices| == 0 {
    assert map_plus_one(indices) == [];
    assert sum_filtered(numbers, []) == 0;
    assert sum_filtered(numbers[1..], []) == 0;
  } else {
    calc {
      sum_filtered(numbers, map_plus_one(indices));
      numbers[map_plus_one(indices)[0]] + sum_filtered(numbers, map_plus_one(indices)[1..]);
      numbers[indices[0] + 1] + sum_filtered(numbers, map_plus_one(indices)[1..]);
      numbers[indices[0] + 1] + sum_filtered(numbers, map_plus_one(indices[1..]));
      {
        lemma_sum_filtered_map_plus_one(numbers, indices[1..]);
      }
      numbers[indices[0] + 1] + sum_filtered(numbers[1..], indices[1..]);
      sum_filtered(numbers[1..], indices);
    }
  }
}

function filter_indices(p: seq<bool>): seq<int>
  ensures forall i :: 0 <= i < |filter_indices(p)| ==> p[filter_indices(p)[i]]
  ensures forall i, j :: 0 <= i < j < |filter_indices(p)| ==> filter_indices(p)[i] < filter_indices(p)[j]
  ensures forall k :: 0 <= k < |p| && p[k] ==> exists j :: 0 <= j < |filter_indices(p)| && filter_indices(p)[j] == k
{
  if |p| == 0 then []
  else
    var rest_filtered := map_plus_one(filter_indices(p[1..]));
    if p[0] then [0] + rest_filtered
    else rest_filtered
}

function map_plus_one(s: seq<int>): seq<int>
  ensures forall i :: 0 <= i < |s| ==> map_plus_one(s)[i] == s[i] + 1
{
  if |s| == 0 then []
  else [s[0] + 1] + map_plus_one(s[1..])
}
// </vc-helpers>

// <vc-spec>
method solution(numbers: seq<int>) returns (s: int)
  // post-conditions-start
  ensures s == sum(numbers, seq(|numbers|, i requires 0 <= i < |numbers| => i % 2 == 0 && numbers[i] % 2 == 1))
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var current_sum := 0;
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant current_sum == sum_filtered(numbers, filter_indices_upto_i(numbers, i))
    decreases |numbers| - i
  {
    if i % 2 == 0 && numbers[i] % 2 == 1 {
      current_sum := current_sum + numbers[i];
    }
    i := i + 1;
  }
  s := current_sum;

  var p_indices_final := seq(|numbers|, k => k % 2 == 0 && numbers[k] % 2 == 1);
  assert current_sum == sum_filtered(numbers, filter_indices(p_indices_final));
  sum_property(numbers, p_indices_final);

  assert s == sum_filtered(numbers, filter_indices(p_indices_final));
  assert s == sum(numbers, p_indices_final);
}
// </vc-code>

function sum(s: seq<int>, p: seq<bool>) : int
  requires |s| == |p|
{
  if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
}
// pure-end