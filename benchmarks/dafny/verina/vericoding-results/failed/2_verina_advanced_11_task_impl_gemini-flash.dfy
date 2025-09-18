// <vc-preamble>
function CountOccurrences(x: int, lst: seq<int>): nat
{
    |set i | 0 <= i < |lst| && lst[i] == x|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed in helper. */
predicate IsMajorityElement(x: int, s: seq<int>) {
  CountOccurrences(x, s) > |s| / 2
}
// </vc-helpers>

// <vc-spec>
method FindMajorityElement(lst: array<int>) returns (result: int)
    ensures var lst_seq := lst[..];
            var n := |lst_seq|;
            var majority := CountOccurrences(result, lst_seq) > n / 2 && 
                          forall x :: CountOccurrences(x, lst_seq) <= n / 2 || x == result;
            (result == -1 ==> forall x :: CountOccurrences(x, lst_seq) <= n / 2) &&
            (result != -1 ==> majority)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error related to missing closing parenthesis in an invariant and addressed a general parsing error. */
{
  var lst_seq := lst[..];
  var n := |lst_seq|;
  if n == 0 {
    return -1;
  }

  var candidate := lst[0];
  var count := 0;
  var start_of_candidate_segment := 0;

  for i := 0 to n
    invariant 0 <= i <= n
    invariant count >= 0
    invariant 0 <= start_of_candidate_segment <= i
    invariant (count > 0) ==> (candidate == lst[start_of_candidate_segment])
    invariant (count > 0) ==> (
        count == CountOccurrences(candidate, lst_seq[start_of_candidate_segment .. i]) - ( (i - start_of_candidate_segment) - CountOccurrences(candidate, lst_seq[start_of_candidate_segment .. i]) )
    )
  {
    if i == n { break; }
    if count == 0 {
      candidate := lst[i];
      count := 1;
      start_of_candidate_segment := i;
    } else if lst[i] == candidate {
      count := count + 1;
    } else {
      count := count - 1;
    }
  }

  var actualCount := 0;
  for i := 0 to n
    invariant 0 <= i <= n
    invariant actualCount == CountOccurrences(candidate, lst_seq[..i])
  {
    if i == n { break; }
    if lst[i] == candidate {
      actualCount := actualCount + 1;
    }
  }

  if actualCount * 2 > n {
    result := candidate;
  } else {
    result := -1;
  }
}
// </vc-code>
