

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
      assert sum(numbers, indices_to_sum) == numbers[0] + sum(rest_numbers, rest_indices_to_sum);
      assert filter_indices(indices_to_sum)[0] == 0;
      assert filter_indices(indices_to_sum)[1..] == map_plus_one(filter_indices(rest_indices_to_sum));
      assert sum_filtered(numbers, filter_indices(indices_to_sum)) == numbers[0] + sum_filtered(numbers, filter_indices(indices_to_sum)[1..]);
      assert sum_filtered(numbers, filter_indices(indices_to_sum)[1..]) == sum_filtered(numbers[1..], filter_indices(rest_indices_to_sum));

      calc {
        sum(numbers, indices_to_sum);
        numbers[0] + sum(rest_numbers, rest_indices_to_sum);
        numbers[0] + sum_filtered(rest_numbers, filter_indices(rest_indices_to_sum));
        sum_filtered(numbers, filter_indices(indices_to_sum)); // Uses properties of sum_filtered combined with filter_indices
      }
    } else {
      assert sum(numbers, indices_to_sum) == sum(rest_numbers, rest_indices_to_sum);
      assert filter_indices(indices_to_sum) == map_plus_one(filter_indices(rest_indices_to_sum));
      assert sum_filtered(numbers, filter_indices(indices_to_sum)) == sum_filtered(numbers[1..], filter_indices(rest_indices_to_sum));

      calc {
        sum(numbers, indices_to_sum);
        sum(rest_numbers, rest_indices_to_sum);
        sum_filtered(rest_numbers, filter_indices(rest_indices_to_sum);
        sum_filtered(numbers, filter_indices(indices_to_sum));
      }
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
    invariant current_sum == sum_filtered(numbers, filter_indices(seq(|numbers|, k requires 0 <= k < i => k % 2 == 0 && numbers[k] % 2 == 1)))
  {
    if i % 2 == 0 && numbers[i] % 2 == 1 {
      current_sum := current_sum + numbers[i];
    }
    i := i + 1;
  }
  s := current_sum;

  // Prove the postcondition
  // The first step is to prove that the loop invariant at termination implies a specific sum_filtered call.
  // Then we use the `sum_property` lemma to bridge sum_filtered to the `sum` function.
  var indices_for_sum := seq(|numbers|, k requires 0 <= k < |numbers| => k % 2 == 0 && numbers[k] % 2 == 1);
  sum_property(numbers, indices_for_sum);

  // Directly assert the postcondition by linking the loop's final state `s` to the desired sum.
  // This relies on the invariant and the sum_property lemma making the connection.
  assert s == sum_filtered(numbers, filter_indices(indices_for_sum));
  assert s == sum(numbers, indices_for_sum);
}
// </vc-code>

function sum(s: seq<int>, p: seq<bool>) : int
  requires |s| == |p|
{
  if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
}
// pure-end