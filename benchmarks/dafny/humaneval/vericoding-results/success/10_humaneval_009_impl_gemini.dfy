// <vc-preamble>

function max_up_to(numbers: seq<int>, index: int): int
    requires 0 <= index < |numbers|
{
    if index == 0 then numbers[0]
    else 
        var prev_max := max_up_to(numbers, index - 1);
        if numbers[index] > prev_max then numbers[index] else prev_max
}
// </vc-preamble>

// <vc-helpers>
lemma max_up_to_is_upper_bound(numbers: seq<int>, i: int)
    requires 0 <= i < |numbers|
    ensures forall j :: 0 <= j <= i ==> numbers[j] <= max_up_to(numbers, i)
{
    if i > 0 {
        max_up_to_is_upper_bound(numbers, i - 1);
    }
}

/* helper modified by LLM (iteration 4): Added explicit base case to fix proof by induction */
lemma max_up_to_exists_in_prefix(numbers: seq<int>, i: int)
    requires 0 <= i < |numbers|
    ensures exists j :: 0 <= j <= i && numbers[j] == max_up_to(numbers, i)
{
    if i == 0 {
        assert max_up_to(numbers, 0) == numbers[0];
    } else {
        max_up_to_exists_in_prefix(numbers, i - 1);
        var prev_max := max_up_to(numbers, i - 1);
        if numbers[i] <= prev_max {
            assert max_up_to(numbers, i) == prev_max;
            assert exists k :: 0 <= k <= i - 1 && numbers[k] == prev_max;
        } else {
            assert max_up_to(numbers, i) == numbers[i];
        }
    }
}
// </vc-helpers>

// <vc-spec>
method rolling_max(numbers: seq<int>) returns (result: seq<int>)
    ensures |result| == |numbers|
    ensures |numbers| == 0 ==> |result| == 0
    ensures |numbers| > 0 ==> |result| > 0
    ensures forall i :: 0 <= i < |result| ==> 
        result[i] == max_up_to(numbers, i)
    ensures forall i :: 0 <= i < |result| ==> 
        forall j :: 0 <= j <= i ==> numbers[j] <= result[i]
    ensures forall i :: 0 <= i < |result| ==> 
        exists j :: 0 <= j <= i && numbers[j] == result[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): No change, code is correct given fixed helpers */
  if |numbers| == 0 {
    result := [];
    return;
  }

  result := [numbers[0]];
  var running_max := numbers[0];
  var i := 1;
  while i < |numbers|
    invariant 1 <= i <= |numbers|
    invariant |result| == i
    invariant running_max == max_up_to(numbers, i - 1)
    invariant forall k :: 0 <= k < i ==> result[k] == max_up_to(numbers, k)
  {
    if numbers[i] > running_max {
      running_max := numbers[i];
    }
    result := result + [running_max];
    i := i + 1;
  }

  forall k | 0 <= k < |numbers|
    ensures forall j :: 0 <= j <= k ==> numbers[j] <= result[k]
    ensures exists j :: 0 <= j <= k && numbers[j] == result[k]
  {
    max_up_to_is_upper_bound(numbers, k);
    max_up_to_exists_in_prefix(numbers, k);
  }
}
// </vc-code>
