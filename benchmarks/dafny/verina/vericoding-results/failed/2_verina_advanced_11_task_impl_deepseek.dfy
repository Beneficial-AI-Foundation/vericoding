// <vc-preamble>
function CountOccurrences(x: int, lst: seq<int>): nat
{
    |set i | 0 <= i < |lst| && lst[i] == x|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix Count function bounds checking */
function Count(index: int, candidate: int, lst: seq<int>): nat
  requires 0 <= index <= |lst|
  decreases |lst| - index
{
  if index >= |lst| then 0
  else (if index < |lst| && lst[index] == candidate then 1 else 0) + Count(index + 1, candidate, lst)
}

lemma CountOccurrencesEquivalence(x: int, lst: seq<int>)
  ensures CountOccurrences(x, lst) == Count(0, x, lst)
{
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
{
  /* code modified by LLM (iteration 5): Fix loop invariant and implement Boyer-Moore voting algorithm */
  var n := lst.Length;
  var lst_seq := lst[..];
  
  if n == 0 {
    result := -1;
    return;
  }
  
  var candidate := lst[0];
  var count := 1;
  var i := 1;
  
  while i < n
    invariant 0 <= i <= n
    invariant count >= 1 ==> (exists j :: 0 <= j < i && lst[j] == candidate)
    invariant count >= 0
    invariant forall k :: 0 <= k < i ==> count >= 0
  {
    if count == 0 {
      candidate := lst[i];
      count := 1;
    } else if lst[i] == candidate {
      count := count + 1;
    } else {
      count := count - 1;
    }
    i := i + 1;
  }
  
  // Verify if candidate is actually majority
  var candidate_count := Count(0, candidate, lst_seq);
  if candidate_count > n / 2 {
    result := candidate;
  } else {
    result := -1;
  }
}
// </vc-code>
